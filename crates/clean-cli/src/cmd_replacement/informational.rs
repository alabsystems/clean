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
//! a `{"stub": true}` placeholder, and reading `unknown` for any row whose
//! evidence is VACUOUS -- an artifact whose producer does not measure the claim
//! (`EvidenceContract::Vacuous`), or a placeholder no command produces
//! (`EvidenceContract::Unproduced`). It is explicitly NOT a launch gate.

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
    /// The file exists and is not a stub, but does not satisfy the contract its
    /// row declares: unparseable, wrong `schema_version`, blank, undeclared, or
    /// reporting its own failure. Opening is not backing.
    Invalid,
    /// The "evidence" is a schema/version name, not a repo path.
    SchemaName,
    /// The path's declared contract is `EvidenceContract::Vacuous` -- its
    /// producer does not measure the row's claim (hard-coded, stub-only or
    /// emit-only), so the row is `Unknown` whatever the file contains -- or it
    /// is `EvidenceContract::Unproduced` and holds the `{"stub": true}`
    /// placeholder no command in the tree will ever replace.
    Vacuous,
}

impl EvidenceState {
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::Present => "present",
            Self::Stub => "STUB",
            Self::Missing => "MISSING",
            Self::Invalid => "INVALID",
            Self::SchemaName => "schema-name",
            Self::Vacuous => "VACUOUS",
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
    /// Every declared evidence path, the ONE location it was read from, and why
    /// it is not `Present` when it is not. Without this a reader cannot tell
    /// which file on which tree produced the verdict.
    pub(crate) evidence_artifacts: Vec<EvidenceArtifactResolution>,
    pub(crate) gate_command: &'static str,
    /// The zero-trust gate that actually backs this row, when one does.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) zero_trust_gate: Option<&'static str>,
    /// That gate's live verdict. When it is not `Passed` the row cannot be
    /// `Green` here, however present and non-stub its evidence file looks.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) zero_trust_gate_status: Option<ZeroTrustGateStatus>,
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct InformationalScorecard {
    pub(crate) schema_version: &'static str,
    pub(crate) note: &'static str,
    /// The single tree every declared artifact was resolved against.
    pub(crate) evidence_root: String,
    /// On whose authority that root was chosen.
    pub(crate) evidence_root_source: &'static str,
    pub(crate) rows: Vec<InformationalRow>,
}

impl InformationalScorecard {
    pub(crate) fn current() -> Self {
        // `replacement_rows()` is now evidence-derived (task M2): each row already
        // carries its measured `evidence_state` and reconciled `effective_status`.
        // This view surfaces both alongside the declared literal, then applies the
        // row's own gate verdict on top (B003).
        //
        // This view must never fail closed, so a trust-core report that cannot be
        // built simply leaves every gate verdict unknown and the rows unchanged.
        let gate_status = zero_trust_gate_status_map();
        let (evidence_root, evidence_root_source) = repo_root_provenance();
        let rows = replacement_rows()
            .into_iter()
            .map(|row| {
                let zero_trust_gate = zero_trust_gate_for_row(row.id);
                let zero_trust_gate_status =
                    zero_trust_gate.and_then(|gate| gate_status.get(gate).copied());
                InformationalRow {
                    id: row.id,
                    area: row.area,
                    declared_status: row.status,
                    effective_status: reconcile_with_gate_verdict(
                        row.effective_status,
                        zero_trust_gate_status,
                    ),
                    evidence_artifact: row.evidence_artifact,
                    evidence_state: row.evidence_state,
                    evidence_artifacts: assess_evidence(row.evidence_artifact).artifacts,
                    gate_command: row.gate_command,
                    zero_trust_gate,
                    zero_trust_gate_status,
                }
            })
            .collect();
        Self {
            schema_version: "clean-replacement-informational-v1",
            note: "INFORMATIONAL ONLY — not a launch gate. The launch gate is the \
                   fail-closed `clean replacement status`. A `green` here means the \
                   row's own evidence file resolves under evidence_root, satisfies \
                   the contract declared for it (parses, carries the expected \
                   schema_version, does not report its own failure) AND, where the \
                   row is backed by a zero-trust gate, that gate reports passed. \
                   `unknown` means the row's evidence is VACUOUS: its producer does \
                   not measure the claim (hard-coded, stub-only or emit-only), or it \
                   is a placeholder no command produces, and the row's detail line \
                   names what would mint real evidence.",
            evidence_root: evidence_root.to_string_lossy().replace('\\', "/"),
            evidence_root_source: evidence_root_source.label(),
            rows,
        }
    }
}

/// The zero-trust gate that decides a row, for rows that have one.
///
/// Mirrors the existing runtime-evidence mapping in
/// `replacement_row_runtime_evidence` (render.rs): these rows already *print*
/// their gate's evidence summary, so reporting a status that contradicts it is
/// indefensible.
pub(crate) fn zero_trust_gate_for_row(row_id: &str) -> Option<&'static str> {
    match row_id {
        "kernel-differential" => Some("kernel-soundness"),
        "fallback-denial" => Some("deny-sorry"),
        _ => None,
    }
}

/// Live zero-trust gate verdicts, empty when the trust-core report cannot build.
fn zero_trust_gate_status_map() -> BTreeMap<&'static str, ZeroTrustGateStatus> {
    TrustCoreEvidenceReport::current()
        .map(|report| {
            report
                .zero_trust_gates
                .iter()
                .map(|gate| (gate.id, gate.status))
                .collect()
        })
        .unwrap_or_default()
}

/// Downgrade a row to match its backing gate. Never upgrades.
///
/// A row whose gate reports `blocked` or `pending_evidence` cannot be `Green`
/// no matter how present its evidence file is: `fallback-denial` was scored
/// Green off a `reports/deny-sorry-launch-evidence.json` recording
/// `ratchet 0/0, status passed`, while the live ratchet is `1/0` and the gate
/// printed `stale: ratchet counts 0/0 do not match current 1/0` in the very
/// same command output.
pub(crate) fn reconcile_with_gate_verdict(
    effective: ReplacementStatus,
    gate_status: Option<ZeroTrustGateStatus>,
) -> ReplacementStatus {
    match gate_status {
        None | Some(ZeroTrustGateStatus::Passed) => effective,
        Some(ZeroTrustGateStatus::Blocked) => ReplacementStatus::Blocked,
        Some(ZeroTrustGateStatus::PendingEvidence) => match effective {
            // Only ever move toward less confidence. `Unknown` stays: it is
            // the absence of information about the row's own evidence, and
            // rewriting it to `PendingEvidence` would drop the VACUOUS reason
            // for a softer word that promises evidence nothing can mint.
            ReplacementStatus::Blocked => ReplacementStatus::Blocked,
            ReplacementStatus::Unknown => ReplacementStatus::Unknown,
            _ => ReplacementStatus::PendingEvidence,
        },
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
        // VACUOUS evidence says nothing about the claim, in either direction,
        // so the row is UNKNOWN whatever was declared -- except `Blocked`,
        // which records a known blocker and is already the least confident
        // claim a row can make. Never an upgrade: `Unknown` is not launch-ready.
        EvidenceState::Vacuous if declared != ReplacementStatus::Blocked => {
            ReplacementStatus::Unknown
        }
        EvidenceState::Missing | EvidenceState::Stub | EvidenceState::Invalid
            if declared == ReplacementStatus::Green =>
        {
            ReplacementStatus::PendingEvidence
        }
        _ => declared,
    }
}

/// Assess a row's declared evidence against the resolved repo root.
///
/// Some rows list SEVERAL artifacts, semicolon-separated (e.g.
/// "docs/RELEASE_READINESS.md; scripts/trust_boundary_expected_tests.txt").
/// Each is resolved and validated on its own and combined fail-closed, so a
/// present sibling never masks a missing, invalid, or stub artifact.
pub(crate) fn assess_evidence(evidence_artifact: &str) -> EvidenceAssessment {
    assess_evidence_in_root(&repo_root(), evidence_artifact)
}

/// Classify a row's declared evidence artifact.
///
/// A file that merely OPENS is not evidence: it must also satisfy the contract
/// declared for it in `evidence_contract_for`. See that module for the measured
/// substitutions this closes.
pub(crate) fn evidence_state_of(evidence_artifact: &str) -> EvidenceState {
    assess_evidence(evidence_artifact).state
}

/// A `{"stub": true}` JSON placeholder is not real evidence.
pub(crate) fn is_stub_evidence(contents: &str) -> bool {
    serde_json::from_str::<serde_json::Value>(contents)
        .ok()
        .and_then(|value| value.get("stub").and_then(serde_json::Value::as_bool))
        .unwrap_or(false)
}

fn status_label(status: ReplacementStatus) -> &'static str {
    status.as_str()
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
        "evidence root: {} ({})",
        scorecard.evidence_root, scorecard.evidence_root_source
    )?;
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
        // Never leave a downgrade unexplained: the reason an artifact failed its
        // contract is the actionable half of the verdict.
        for artifact in &row.evidence_artifacts {
            if let Some(detail) = &artifact.detail {
                writeln!(out, "  {:<28} └─ {}: {}", "", artifact.declared, detail)?;
            }
        }
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
        // VACUOUS evidence reads `Unknown` rather than `PendingEvidence`
        // (2026-09-24): it is not evidence that is late, it is evidence whose
        // producer does not measure the claim.
        for row in &scorecard.rows {
            if row.declared_status == ReplacementStatus::Green
                && row.evidence_state != EvidenceState::Present
            {
                let want = if row.evidence_state == EvidenceState::Vacuous {
                    ReplacementStatus::Unknown
                } else {
                    ReplacementStatus::PendingEvidence
                };
                assert_eq!(
                    row.effective_status, want,
                    "row {} claims green on {:?} evidence",
                    row.id, row.evidence_state
                );
            }
        }
    }

    #[test]
    fn evidence_state_handles_semicolon_separated_artifact_lists() {
        // Regression: a multi-path evidence list used to be read as ONE path,
        // so rows reported Missing even when every file existed.
        assert_eq!(
            evidence_state_of("docs/RELEASE_READINESS.md"),
            EvidenceState::Present,
            "single existing path must be Present"
        );
        assert_eq!(
            evidence_state_of("docs/RELEASE_READINESS.md; docs/SOUNDNESS_CERTIFICATE.md"),
            EvidenceState::Present,
            "every listed path exists, so the row has its declared evidence"
        );
        // Fail-closed: one absent path condemns the whole list.
        assert_eq!(
            evidence_state_of("docs/RELEASE_READINESS.md; docs/definitely_not_a_real_file.md"),
            EvidenceState::Missing,
            "a missing path must not be masked by a present sibling"
        );
        assert_eq!(
            evidence_state_of("clean-replacement-status-v1"),
            EvidenceState::SchemaName,
            "schema-name evidence carries no path separator"
        );
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
