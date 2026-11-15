// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! What a row's declared evidence artifact must *contain* to count as evidence.
//!
//! Before this module existed, an artifact scored `present` whenever the file
//! merely opened and was not the literal `{"stub": true}`. Measured by
//! substitution onto `reports/compile-runtime-smoke.json` (2026-08-26, release
//! binary): a **zero-byte** file, **non-JSON prose**, and JSON reading
//! `{"status":"FAILED"}` each scored the `compile-runtime` row
//! `effective=Green evidence_state=present`. An artifact that reports its own
//! failure was the gate's proof that the row passed.
//!
//! So evidence is now *validated against a declared contract*, not merely
//! opened. The contract is the same notion of validity `clean replacement
//! validate-report` applies — `ReplacementReportKind::expected_schema()` — and
//! `evidence_contract_agrees_with_validate_report_kinds` in the tests binds the
//! two together so they cannot drift apart.
//!
//! Resolution is deterministic and recorded: see [`repo_root_provenance`].
//! A path with **no declared contract** is not evidence either; that is a
//! fail-closed default, so a new row must say what its artifact is.

use super::*;

/// What a declared evidence artifact must contain to back a row.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum EvidenceContract {
    /// A JSON report carrying exactly this `schema_version`, which must not
    /// report its own failure.
    JsonReport { schema_version: &'static str },
    /// A prose document (Markdown / text). Must not be blank.
    Document,
    /// An artifact whose PRODUCER does not measure the row's claim --
    /// hard-coded, stub-only or emit-only evidence. However well-formed the
    /// file is, it cannot back a row: the row reads `unknown`, never `green`.
    /// `why` says what the artifact actually is; `would_mint` names what would
    /// produce real evidence, so the downgrade is actionable rather than a
    /// verdict nobody can discharge.
    Vacuous {
        why: &'static str,
        would_mint: &'static str,
    },
    /// A JSON report contract that NO command in the tree produces yet. Real
    /// content is validated exactly as `JsonReport { schema_version }`, but the
    /// `{"stub": true}` placeholder standing at the path is VACUOUS rather than
    /// late -- nothing will replace it until a producer exists -- so the row
    /// reads `unknown`, and `would_mint` names the producer that would change
    /// that. Unlike `Vacuous`, a real report minted later backs the row with no
    /// contract change: what is vacuous here is the placeholder, not the path.
    Unproduced {
        schema_version: &'static str,
        would_mint: &'static str,
    },
}

#[cfg(test)]
impl EvidenceContract {
    /// The `schema_version` a real artifact at this path must carry, for the
    /// contracts that validate one. Test-only: it is how
    /// `evidence_contract_agrees_with_validate_report_kinds` compares both
    /// JSON-validating contracts against `validate-report`'s schema pin.
    pub(crate) fn json_schema(self) -> Option<&'static str> {
        match self {
            Self::JsonReport { schema_version } | Self::Unproduced { schema_version, .. } => {
                Some(schema_version)
            }
            Self::Document | Self::Vacuous { .. } => None,
        }
    }
}

/// The tactic-parity count artifact, measured 2026-09-24 (lean4-replacement
/// audit, tactics pillar, re-measured before this change): every one of its
/// 56 rows reads `"matched": true`, and that value is a LITERAL -- `matched:
/// true` sits in the production source of `generated_cases.rs` (five sites),
/// `generated_cases_ext.rs` (two) and `tactic_rows.rs` (one); every
/// `lean4_fixture` is a label string such as
/// `generated:lean4-simp-representative`, and pinned Lean is never run. The
/// artifact itself says `full_lean4_corpus_coverage_claimed: false`. It
/// scored the `tactic-parity` row GREEN in `clean replacement status
/// --informational` all the same.
pub(crate) const TACTIC_PARITY_COUNTS_VACUOUS: EvidenceContract = EvidenceContract::Vacuous {
    why: "every row's `matched: true` is a literal in cmd_replacement/generated_cases*.rs and \
          tactic_rows.rs, every `lean4_fixture` is a label string, and pinned Lean is never run",
    would_mint: "a differential tactic battery whose every expectation the pinned Lean \
                 v4.30.0-rc2 produced, weighted by Mathlib tactic usage; no command mints one \
                 yet (reports/tactic-parity-full-corpus.json, the artifact `clean replacement \
                 tactic-parity validate-full-corpus` checks, is itself a stub)",
};

/// The LSP/infoview parity report, measured 2026-09-25 before this change: the
/// file is the 15-byte `{"stub": true}` placeholder, and nothing in the tree
/// WRITES a `clean-lsp-infoview-parity-v1` report -- `git grep` finds that
/// schema only in two validators (`clean replacement validate-report` and
/// `crates/clean-lsp/src/report_validation.rs`, whose tests all skip on the
/// stub and pin that they do). The row was never Green (it is declared
/// `PendingEvidence`), but "pending" promised evidence that no command can
/// mint, so it reads `unknown` now, naming the harness that would mint it.
pub(crate) const LSP_INFOVIEW_PARITY_UNPRODUCED: EvidenceContract = EvidenceContract::Unproduced {
    schema_version: "clean-lsp-infoview-parity-v1",
    would_mint: "a harness that drives `clean lsp` over a recorded vscode-lean4 session \
                 (initialize, didOpen, hover, plainGoal, getInteractiveGoals) beside pinned \
                 Lean v4.30.0-rc2's server and writes that report with its measured rows \
                 (docs/plans/AUDIT_PILLARS_2026-08-10.md sizes it); `clean replacement \
                 validate-report --kind lsp-infoview` then checks it and this row reads its \
                 real state",
};

/// The declared contract for an evidence path, or `None` when the path has
/// never been declared. `None` is fail-closed: an undeclared artifact cannot
/// make a row green, however present the file is.
pub(crate) fn evidence_contract_for(path: &str) -> Option<EvidenceContract> {
    let json = |schema_version| Some(EvidenceContract::JsonReport { schema_version });
    match path {
        "reports/kernel-soundness-launch-evidence.json" => {
            json("clean-kernel-soundness-launch-evidence-v1")
        }
        "reports/deny-sorry-launch-evidence.json" => json("clean-deny-sorry-launch-evidence-v1"),
        "reports/axiom-audit-launch-evidence.json" => json("clean-axiom-audit-launch-evidence-v1"),
        "reports/tactic-parity-counts.json" => Some(TACTIC_PARITY_COUNTS_VACUOUS),
        "reports/strict-solver-fragment-dashboard.json" => {
            json("clean-strict-solver-fragment-dashboard-v1")
        }
        "reports/native-library-replacement.json" => json("clean-native-library-replacement-v1"),
        "reports/mathverse-replay-replacement.json" => {
            json("clean-mathverse-replay-replacement-v1")
        }
        "reports/lsp-infoview-parity.json" => Some(LSP_INFOVIEW_PARITY_UNPRODUCED),
        "reports/lake-replacement-smoke.json" => json("clean-lake-replacement-smoke-v1"),
        "reports/compile-runtime-smoke.json" => json("clean-compile-runtime-smoke-v1"),
        "reports/native-exec-battery.json" => json("clean-native-exec-battery-v1"),
        "reports/rust-first-tooling.json" => json("clean-rust-first-tooling-evidence-v1"),
        // The benchmark publication artifact predates the `clean-*-v1` naming
        // convention and pins an integer `schema_version`; compared by value.
        "reports/benchmarks/publication/current.json" => json("1"),
        "tests/lean4_compat/frontend_replacement_scorecard.json" => {
            json("clean-frontend-parity-scorecard-v1")
        }
        "docs/RELEASE_READINESS.md"
        | "docs/SOUNDNESS_CERTIFICATE.md"
        | "docs/VERIFICATION_AUDIT.md"
        | "scripts/trust_boundary_expected_tests.txt" => Some(EvidenceContract::Document),
        _ => None,
    }
}

/// Self-reported-status fields, and the values that mean "this artifact is
/// telling you it did not pass".
///
/// `launch_ready: false` is deliberately **not** in here: an honest in-progress
/// artifact says exactly that, and reading it as a failure would punish honesty.
const STATUS_FIELDS: &[&str] = &[
    "status",
    "overall_status",
    "validation_status",
    "gate_status",
];
const FAILURE_STATUSES: &[&str] = &[
    "failed", "fail", "failing", "error", "errored", "invalid", "rejected", "blocked", "stale",
    "missing", "aborted", "timeout",
];
/// Boolean fields whose `false` is the artifact reporting its own failure.
const PASSED_FIELDS: &[&str] = &["passed", "validation_passed"];

/// Validate `contents` against the contract declared for `path`.
///
/// `Ok(())` means the artifact really backs its row. `Err(detail)` names the
/// reason, which is carried into the scorecard output rather than discarded.
pub(crate) fn validate_evidence_artifact(path: &str, contents: &str) -> Result<(), String> {
    let Some(contract) = evidence_contract_for(path) else {
        return Err(format!(
            "no declared evidence contract for {path}; declare one in \
             evidence_contract_for before it can back a row"
        ));
    };
    match contract {
        EvidenceContract::Document => {
            if contents.trim().is_empty() {
                Err("document is empty".to_owned())
            } else {
                Ok(())
            }
        }
        EvidenceContract::JsonReport { schema_version } => {
            validate_json_evidence(contents, schema_version)
        }
        EvidenceContract::Vacuous { why, would_mint } => Err(vacuous_detail(why, would_mint)),
        EvidenceContract::Unproduced {
            schema_version,
            would_mint,
        } => {
            if is_stub_evidence(contents) {
                Err(unproduced_stub_detail(schema_version, would_mint))
            } else {
                validate_json_evidence(contents, schema_version)
            }
        }
    }
}

/// The one sentence a VACUOUS artifact carries into the scorecard.
pub(crate) fn vacuous_detail(why: &str, would_mint: &str) -> String {
    format!("VACUOUS -- {why}; real evidence would be {would_mint}")
}

/// The VACUOUS sentence for the placeholder standing at an `Unproduced` path.
pub(crate) fn unproduced_stub_detail(schema_version: &str, would_mint: &str) -> String {
    vacuous_detail(
        &format!(
            "the artifact is the `{{\"stub\": true}}` placeholder and no command in the tree \
             produces a {schema_version} report"
        ),
        would_mint,
    )
}

fn validate_json_evidence(contents: &str, expected_schema: &str) -> Result<(), String> {
    let value: serde_json::Value =
        serde_json::from_str(contents).map_err(|error| format!("not valid JSON: {error}"))?;
    let Some(object) = value.as_object() else {
        return Err("not a JSON object".to_owned());
    };

    let observed = object
        .get("schema_version")
        .map(json_scalar_string)
        .unwrap_or_default();
    if observed != expected_schema {
        return Err(format!(
            "schema_version expected {expected_schema}, observed {}",
            missing_string(&observed)
        ));
    }

    for field in STATUS_FIELDS {
        let Some(status) = object.get(*field).and_then(serde_json::Value::as_str) else {
            continue;
        };
        if FAILURE_STATUSES.contains(&status.to_ascii_lowercase().as_str()) {
            return Err(format!(
                "artifact reports its own failure: {field}={status}"
            ));
        }
    }
    for field in PASSED_FIELDS {
        if object.get(*field).and_then(serde_json::Value::as_bool) == Some(false) {
            return Err(format!("artifact reports its own failure: {field}=false"));
        }
    }
    Ok(())
}

/// Render a scalar JSON value as the string the contract compares against, so
/// an integer `schema_version: 1` and a string `"1"` are the same pin.
fn json_scalar_string(value: &serde_json::Value) -> String {
    match value {
        serde_json::Value::String(text) => text.clone(),
        other => other.to_string(),
    }
}

/// One declared evidence path, where it resolved, and what it was found to be.
///
/// This is the provenance half of the fix: a run can no longer score a row off
/// a file whose location nobody recorded.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct EvidenceArtifactResolution {
    /// The path exactly as the row declares it.
    pub(crate) declared: String,
    /// The single path the gate actually read, absolute and unambiguous.
    pub(crate) resolved_path: String,
    pub(crate) state: EvidenceState,
    /// Why the artifact is not `Present`; absent when it is.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub(crate) detail: Option<String>,
}

/// The verdict over a row's whole (possibly semicolon-separated) evidence list,
/// plus the per-path provenance behind it.
#[derive(Debug, Clone, Serialize)]
pub(crate) struct EvidenceAssessment {
    pub(crate) state: EvidenceState,
    pub(crate) artifacts: Vec<EvidenceArtifactResolution>,
}

/// Assess a row's declared evidence against an explicit repo root.
///
/// Taking the root as a parameter is what makes the substitution test in
/// `tests/part_16.rs` hermetic: it can point the real assessment at a temp
/// directory instead of mutating the shared working tree.
pub(crate) fn assess_evidence_in_root(root: &Path, evidence_artifact: &str) -> EvidenceAssessment {
    // Schema-name "evidence" (e.g. "clean-replacement-status-v1") carries no
    // path separator and is validated by the row's gate command, not by a file.
    if !evidence_artifact.contains('/') {
        return EvidenceAssessment {
            state: EvidenceState::SchemaName,
            artifacts: Vec::new(),
        };
    }

    let mut artifacts = Vec::new();
    for declared in evidence_artifact.split(';') {
        let declared = declared.trim();
        if declared.is_empty() || !declared.contains('/') {
            continue;
        }
        artifacts.push(assess_one_artifact(root, declared));
    }
    if artifacts.is_empty() {
        return EvidenceAssessment {
            state: EvidenceState::SchemaName,
            artifacts,
        };
    }

    // Fail-closed precedence: the worst path decides the row. A present sibling
    // never masks a missing, invalid, or stub artifact.
    let state = [
        EvidenceState::Missing,
        EvidenceState::Invalid,
        EvidenceState::Stub,
        EvidenceState::Vacuous,
    ]
    .into_iter()
    .find(|worst| artifacts.iter().any(|artifact| artifact.state == *worst))
    .unwrap_or(EvidenceState::Present);

    EvidenceAssessment { state, artifacts }
}

fn assess_one_artifact(root: &Path, declared: &str) -> EvidenceArtifactResolution {
    let resolved = root.join(declared);
    let resolution = |state, detail: Option<String>| EvidenceArtifactResolution {
        declared: declared.to_owned(),
        resolved_path: resolved.to_string_lossy().replace('\\', "/"),
        state,
        detail,
    };

    // A VACUOUS path is decided by what PRODUCES it, not by what it contains:
    // no content at that path -- the committed file, a perfectly shaped report,
    // or nothing at all -- can back a row until the contract changes.
    if let Some(EvidenceContract::Vacuous { why, would_mint }) = evidence_contract_for(declared) {
        return resolution(
            EvidenceState::Vacuous,
            Some(vacuous_detail(why, would_mint)),
        );
    }

    let contents = match fs::read_to_string(&resolved) {
        Ok(contents) => contents,
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            return resolution(EvidenceState::Missing, Some("file not found".to_owned()));
        }
        Err(error) => {
            return resolution(EvidenceState::Invalid, Some(format!("unreadable: {error}")));
        }
    };

    if is_stub_evidence(&contents) {
        // A placeholder where no producer exists is not evidence that is late:
        // nothing will ever replace it, so it reads VACUOUS, naming the
        // producer that would (`EvidenceContract::Unproduced`).
        if let Some(EvidenceContract::Unproduced {
            schema_version,
            would_mint,
        }) = evidence_contract_for(declared)
        {
            return resolution(
                EvidenceState::Vacuous,
                Some(unproduced_stub_detail(schema_version, would_mint)),
            );
        }
        return resolution(
            EvidenceState::Stub,
            Some("`{\"stub\": true}` placeholder".to_owned()),
        );
    }

    match validate_evidence_artifact(declared, &contents) {
        Ok(()) => resolution(EvidenceState::Present, None),
        Err(detail) => resolution(EvidenceState::Invalid, Some(detail)),
    }
}
