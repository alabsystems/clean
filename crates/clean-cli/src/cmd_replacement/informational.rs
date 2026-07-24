// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Informational replacement scorecard for AI-agent navigation.
//!
//! `ReplacementStatusReport::current()` is a fail-closed *trust gate*: it errors
//! when soundness evidence is missing, which is correct for a gate but useless
//! for an agent trying to *learn* Clean's Lean-4-replacement status. This view
//! never fails closed — it renders every replacement row with its real evidence
//! state, downgrading any hand-declared `Green` whose evidence file is absent or
//! a `{"stub": true}` placeholder. It is explicitly NOT a launch gate.

use super::*;

/// Whether a row's declared evidence artifact actually backs it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum EvidenceState {
    /// The evidence file exists and is not a stub.
    Present,
    /// The evidence file exists but is a `{"stub": true}` placeholder.
    Stub,
    /// The declared evidence file does not exist.
    Missing,
    /// The "evidence" is a schema/version name, not a repo path.
    SchemaName,
}

impl EvidenceState {
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::Present => "present",
            Self::Stub => "STUB",
            Self::Missing => "MISSING",
            Self::SchemaName => "schema-name",
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct InformationalRow {
    pub(crate) id: &'static str,
    pub(crate) area: &'static str,
    /// The status literal declared in `replacement_rows()`.
    pub(crate) declared_status: ReplacementStatus,
    /// The honest status: a declared `Green` is downgraded to `PendingEvidence`
    /// unless its own evidence file is actually `Present`.
    pub(crate) effective_status: ReplacementStatus,
    pub(crate) evidence_artifact: &'static str,
    pub(crate) evidence_state: EvidenceState,
    pub(crate) gate_command: &'static str,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct InformationalScorecard {
    pub(crate) schema_version: &'static str,
    pub(crate) note: &'static str,
    pub(crate) rows: Vec<InformationalRow>,
}

impl InformationalScorecard {
    pub(crate) fn current() -> Self {
        // `replacement_rows()` is now evidence-derived (task M2): each row already
        // carries its measured `evidence_state` and reconciled `effective_status`.
        // This view simply surfaces both alongside the declared literal.
        let rows = replacement_rows()
            .into_iter()
            .map(|row| InformationalRow {
                id: row.id,
                area: row.area,
                declared_status: row.status,
                effective_status: row.effective_status,
                evidence_artifact: row.evidence_artifact,
                evidence_state: row.evidence_state,
                gate_command: row.gate_command,
            })
            .collect();
        Self {
            schema_version: "clean-replacement-informational-v1",
            note: "INFORMATIONAL ONLY — not a launch gate. The launch gate is the \
                   fail-closed `clean replacement status`. A `green` here means the \
                   row's own evidence file is present and non-stub.",
            rows,
        }
    }
}

/// Reconcile a row's declared status against its measured evidence state (M2).
///
/// This is the heart of the evidence-derived scorecard: a hand-declared `Green`
/// is downgraded to `PendingEvidence` whenever its file-backed evidence is
/// missing or a `{"stub": true}` placeholder. We never *upgrade* on evidence
/// presence — a row becomes `Green` only by the human declaring it *and* the
/// evidence backing it. Schema-name "evidence" (no path separator) is validated
/// by the row's gate command / trust-core path, not by file presence, so those
/// rows keep their declared status here.
pub(crate) fn effective_status_for(
    declared: ReplacementStatus,
    evidence_state: EvidenceState,
) -> ReplacementStatus {
    match evidence_state {
        EvidenceState::Missing | EvidenceState::Stub if declared == ReplacementStatus::Green => {
            ReplacementStatus::PendingEvidence
        }
        _ => declared,
    }
}

/// Classify a row's declared evidence artifact.
pub(crate) fn evidence_state_of(evidence_artifact: &'static str) -> EvidenceState {
    // The launch-critical rows point at a single repo path; schema-name evidence
    // (e.g. "clean-replacement-status-v1") carries no path separator.
    if !evidence_artifact.contains('/') {
        return EvidenceState::SchemaName;
    }
    match read_optional_repo_artifact(evidence_artifact) {
        Ok(Some(contents)) if is_stub_evidence(&contents) => EvidenceState::Stub,
        Ok(Some(_)) => EvidenceState::Present,
        _ => EvidenceState::Missing,
    }
}

/// A `{"stub": true}` JSON placeholder is not real evidence.
pub(crate) fn is_stub_evidence(contents: &str) -> bool {
    serde_json::from_str::<serde_json::Value>(contents)
        .ok()
        .and_then(|value| value.get("stub").and_then(serde_json::Value::as_bool))
        .unwrap_or(false)
}

fn status_label(status: ReplacementStatus) -> &'static str {
    match status {
        ReplacementStatus::Green => "green",
        ReplacementStatus::InProgress => "in_progress",
        ReplacementStatus::PendingEvidence => "pending_evidence",
        ReplacementStatus::Blocked => "blocked",
    }
}

pub(crate) fn render_informational_human(
    out: &mut impl Write,
    scorecard: &InformationalScorecard,
) -> io::Result<()> {
    writeln!(
        out,
        "Lean 4 replacement scorecard (INFORMATIONAL — not a launch gate)"
    )?;
    writeln!(out, "{}", scorecard.note)?;
    writeln!(out)?;
    writeln!(
        out,
        "  {:<28} {:<16} {:<12} ARTIFACT",
        "AREA", "STATUS", "EVIDENCE"
    )?;
    for row in &scorecard.rows {
        writeln!(
            out,
            "  {:<28} {:<16} {:<12} {}",
            row.id,
            status_label(row.effective_status),
            row.evidence_state.label(),
            row.evidence_artifact,
        )?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn informational_view_downgrades_stub_backed_green_rows() {
        let scorecard = InformationalScorecard::current();
        // Every row whose declared status is Green but whose evidence is not
        // Present must be downgraded — never reported green on stub/missing.
        for row in &scorecard.rows {
            if row.declared_status == ReplacementStatus::Green
                && row.evidence_state != EvidenceState::Present
            {
                assert_eq!(
                    row.effective_status,
                    ReplacementStatus::PendingEvidence,
                    "row {} claims green on {:?} evidence",
                    row.id,
                    row.evidence_state
                );
            }
        }
    }

    #[test]
    fn informational_view_never_panics_and_lists_all_rows() {
        let scorecard = InformationalScorecard::current();
        assert_eq!(scorecard.rows.len(), replacement_rows().len());
        let mut buf = Vec::new();
        render_informational_human(&mut buf, &scorecard).expect("render");
        let text = String::from_utf8(buf).expect("utf8");
        assert!(text.contains("INFORMATIONAL"));
    }
}
