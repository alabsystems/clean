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
}

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
        "reports/tactic-parity-counts.json" => json("clean-tactic-parity-count-artifact-v1"),
        "reports/strict-solver-fragment-dashboard.json" => {
            json("clean-strict-solver-fragment-dashboard-v1")
        }
        "reports/native-library-replacement.json" => json("clean-native-library-replacement-v1"),
        "reports/mathverse-replay-replacement.json" => {
            json("clean-mathverse-replay-replacement-v1")
        }
        "reports/lsp-infoview-parity.json" => json("clean-lsp-infoview-parity-v1"),
        "reports/lake-replacement-smoke.json" => json("clean-lake-replacement-smoke-v1"),
        "reports/compile-runtime-smoke.json" => json("clean-compile-runtime-smoke-v1"),
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
    }
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
