// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Emitter for the `rust-first-tooling` row evidence artifact.
//!
//! The scorecard row expects `reports/rust-first-tooling.json`, but until this
//! module existed nothing could mint it: `rust_first_tooling_status()` computed
//! the per-lane inventory and then only ever serialized it inside the live
//! `clean replacement status` report. This emitter persists that same computed
//! state as a standalone evidence artifact, with build provenance
//! (`generated_at_commit`) and the committed command that regenerates it.
//!
//! Honesty contract: the artifact records what `rust_first_tooling_status()`
//! returns — nothing more. It carries no top-level `launch_ready` key (so it
//! can never be misread as a replacement-launch claim by
//! `report_claims_launch_readiness`-shaped scanners), and the write path is
//! guarded twice: by the B001 stale-binary refusal and by a fail-closed check
//! that refuses to mint evidence while any replacement-critical lane is not
//! Rust-owned or demoted.

use super::*;

/// The persisted shape of `reports/rust-first-tooling.json`.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct RustFirstToolingEvidenceArtifact {
    pub(crate) schema_version: &'static str,
    pub(crate) generated_by: &'static str,
    pub(crate) generated_at: String,
    /// Commit the emitting binary was built at (`CLEAN_BUILD_GIT_SHA`). The
    /// write path proves this equals HEAD via [`validate_binary_matches_head`];
    /// a print-only run may honestly record `unknown`.
    pub(crate) generated_at_commit: String,
    pub(crate) gate_command: &'static str,
    pub(crate) evidence_artifact: &'static str,
    pub(crate) replacement_row: &'static str,
    pub(crate) non_claim: &'static str,
    pub(crate) rust_first_tooling: RustFirstToolingStatus,
}

const RUST_FIRST_TOOLING_NON_CLAIM: &str =
    "This artifact records the computed Rust-first tooling migration inventory only. It does \
     not claim replacement launch readiness; the fail-closed launch gate remains `clean \
     replacement status`.";

impl RustFirstToolingEvidenceArtifact {
    pub(crate) fn current() -> Self {
        Self::from_status(rust_first_tooling_status())
    }

    pub(crate) fn from_status(status: RustFirstToolingStatus) -> Self {
        Self {
            schema_version: RUST_FIRST_TOOLING_EVIDENCE_SCHEMA_VERSION,
            generated_by: "clean replacement rust-first-tooling",
            generated_at: utc_timestamp_seconds(),
            generated_at_commit: option_env!("CLEAN_BUILD_GIT_SHA")
                .unwrap_or("unknown")
                .to_string(),
            gate_command: RUST_FIRST_TOOLING_GATE_COMMAND,
            evidence_artifact: RUST_FIRST_TOOLING_EVIDENCE_PATH,
            replacement_row: "rust-first-tooling",
            non_claim: RUST_FIRST_TOOLING_NON_CLAIM,
            rust_first_tooling: status,
        }
    }
}

/// Fail-closed guard on the evidence WRITE: the artifact's presence backs the
/// `rust-first-tooling` scorecard row, so it may only be minted while every
/// replacement-critical lane is Rust-owned or demoted. Kept pure (no I/O) so
/// the refusal branch is unit-testable with an injected non-ready status.
pub(crate) fn rust_first_tooling_write_refusal(
    status: &RustFirstToolingStatus,
) -> Result<(), String> {
    if status.launch_ready {
        return Ok(());
    }
    let blocking: Vec<&str> = status
        .commands
        .iter()
        .filter(|row| {
            row.status != ToolMigrationStatus::RustOwned
                && row.status != ToolMigrationStatus::Demoted
        })
        .map(|row| row.id)
        .collect();
    Err(format!(
        "rust-first tooling inventory is not launch_ready (overall_status={}); refusing to \
         mint {RUST_FIRST_TOOLING_EVIDENCE_PATH} while lanes [{}] are not Rust-owned or demoted",
        status.overall_status.as_str(),
        blocking.join(", ")
    ))
}

pub(crate) fn run_rust_first_tooling(
    args: RustFirstToolingEvidenceArgs,
) -> Result<(), ReplacementError> {
    let artifact = RustFirstToolingEvidenceArtifact::current();

    if let Some(evidence_path) = &args.evidence {
        // B001: only the WRITE is guarded (matching axiom-audit): printing the
        // inventory from any binary is harmless, but a persisted evidence
        // artifact attributes a verdict to a commit, so it must come from a
        // binary built at that commit.
        validate_binary_matches_head()?;
        rust_first_tooling_write_refusal(&artifact.rust_first_tooling)
            .map_err(|message| ReplacementError::ReportValidation { message })?;
        write_json_path(evidence_path, &artifact)?;
    }

    let stdout = io::stdout();
    let mut out = stdout.lock();
    if args.json {
        writeln!(
            out,
            "{}",
            serde_json::to_string_pretty(&artifact).map_err(ReplacementError::Serialize)?
        )?;
    } else {
        render_rust_first_tooling_human(&mut out, &artifact, args.evidence.as_deref())?;
    }
    Ok(())
}

pub(crate) fn render_rust_first_tooling_human(
    out: &mut impl Write,
    artifact: &RustFirstToolingEvidenceArtifact,
    evidence_path: Option<&Path>,
) -> Result<(), ReplacementError> {
    writeln!(out, "clean rust-first tooling evidence")?;
    writeln!(out, "schema_version: {}", artifact.schema_version)?;
    writeln!(out, "generated_at_commit: {}", artifact.generated_at_commit)?;
    writeln!(
        out,
        "launch_ready: {}",
        artifact.rust_first_tooling.launch_ready
    )?;
    writeln!(
        out,
        "overall_status: {}",
        artifact.rust_first_tooling.overall_status.as_str()
    )?;
    for row in &artifact.rust_first_tooling.commands {
        writeln!(out, "- {} [{}]", row.id, row.status.as_str())?;
    }
    if let Some(path) = evidence_path {
        writeln!(out, "wrote: {}", path.display())?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_artifact_current_records_computed_status_and_lanes() {
        let artifact = RustFirstToolingEvidenceArtifact::current();
        let status = rust_first_tooling_status();
        assert_eq!(
            artifact.schema_version,
            RUST_FIRST_TOOLING_EVIDENCE_SCHEMA_VERSION
        );
        assert_eq!(artifact.replacement_row, "rust-first-tooling");
        assert_eq!(artifact.evidence_artifact, RUST_FIRST_TOOLING_EVIDENCE_PATH);
        assert_eq!(
            artifact.rust_first_tooling.launch_ready, status.launch_ready,
            "the artifact must record exactly what rust_first_tooling_status computed"
        );
        assert_eq!(
            artifact.rust_first_tooling.commands.len(),
            status.commands.len()
        );
        assert!(!artifact.rust_first_tooling.commands.is_empty());
    }

    #[test]
    fn test_artifact_json_is_non_stub_and_carries_per_lane_entries() {
        let artifact = RustFirstToolingEvidenceArtifact::current();
        let rendered = serde_json::to_string_pretty(&artifact).expect("artifact should serialize");
        assert!(
            !is_stub_evidence(&rendered),
            "evidence must not read as a stub placeholder"
        );
        let value: serde_json::Value =
            serde_json::from_str(&rendered).expect("artifact JSON should round-trip");
        assert_eq!(
            value["schema_version"],
            RUST_FIRST_TOOLING_EVIDENCE_SCHEMA_VERSION
        );
        assert!(value["generated_at_commit"].is_string());
        assert_eq!(value["gate_command"], RUST_FIRST_TOOLING_GATE_COMMAND);
        let lanes = value["rust_first_tooling"]["commands"]
            .as_array()
            .expect("per-lane entries should be present");
        assert_eq!(lanes.len(), python_tool_migration_rows().len());
        assert!(lanes
            .iter()
            .all(|lane| lane["id"].is_string() && lane["status"].is_string()));
        // Never a top-level launch_ready key: the artifact must not be readable
        // as a replacement launch-readiness claim.
        assert!(value.get("launch_ready").is_none());
    }

    #[test]
    fn test_write_refusal_rejects_non_rust_owned_lane() {
        let mut status = rust_first_tooling_status();
        status.launch_ready = false;
        status.overall_status = ToolMigrationStatus::Transitional;
        if let Some(row) = status.commands.first_mut() {
            row.status = ToolMigrationStatus::Transitional;
        }
        let message = rust_first_tooling_write_refusal(&status)
            .expect_err("non-ready inventory must refuse the evidence write");
        assert!(message.contains("not launch_ready"));
        assert!(message.contains(RUST_FIRST_TOOLING_EVIDENCE_PATH));
    }

    #[test]
    fn test_write_refusal_accepts_computed_ready_status() {
        let status = rust_first_tooling_status();
        assert!(
            status.launch_ready,
            "current inventory has every lane RustOwned/Demoted"
        );
        rust_first_tooling_write_refusal(&status).expect("ready inventory must pass");
    }
}
