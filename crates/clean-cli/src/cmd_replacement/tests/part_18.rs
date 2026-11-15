// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Evidence-validation substitution battery (slice 18).
//!
//! THE DEFECT THIS EXISTS FOR (measured 2026-08-26, release binary at c0ea930ca):
//! `evidence_state_of` scored an artifact `present` whenever the file merely
//! OPENED and was not the literal `{"stub": true}`. Substituted onto
//! `reports/compile-runtime-smoke.json`, each of a **zero-byte** file,
//! **non-JSON prose**, and `{"status":"FAILED"}` scored the `compile-runtime`
//! row `effective=Green evidence_state=present`. Separately, `repo_artifact_path`
//! resolved cwd-FIRST with a silent fallback, so running from a `/tmp` directory
//! holding three EMPTY files scored `tactic-parity`, `strict-reconstruction` and
//! `compile-runtime` all green — three of the four effectively-green rows.
//!
//! Every arm below is two-way on purpose: it first asserts the REAL artifact
//! content is `Present`, then substitutes and asserts it is not. A one-way arm
//! would pass against a gate that says no to everything.

use crate::cmd_replacement::*;

/// The artifacts that actually carried effectively-green rows.
///
/// `reports/tactic-parity-counts.json` was the third, and left this list on
/// 2026-09-24: its contract is now `EvidenceContract::Vacuous` (its `matched:
/// true` rows are source literals and pinned Lean is never run), so arm 5's
/// "the real content is Present" no longer holds of it BY DESIGN -- no content
/// at that path backs a row. Slice 20 pins that instead.
const SUBSTITUTION_TARGETS: &[&str] = &[
    "reports/compile-runtime-smoke.json",
    "reports/strict-solver-fragment-dashboard.json",
];

/// A private scratch tree, so the battery never mutates the shared worktree.
struct EvidenceTree {
    root: PathBuf,
}

impl EvidenceTree {
    fn new(tag: &str) -> Self {
        let root = std::env::temp_dir().join(format!(
            "clean-evidence-substitution-{tag}-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).expect("create scratch evidence root");
        Self { root }
    }

    fn write(&self, relative: &str, contents: &str) {
        let path = self.root.join(relative);
        fs::create_dir_all(path.parent().expect("artifact parent"))
            .expect("create artifact directory");
        fs::write(&path, contents).expect("write substituted artifact");
    }

    fn state_of(&self, artifact: &str) -> EvidenceState {
        assess_evidence_in_root(&self.root, artifact).state
    }
}

impl Drop for EvidenceTree {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

/// The genuine committed artifact, read from the real repo root.
fn real_artifact(relative: &str) -> String {
    fs::read_to_string(repo_artifact_path(relative))
        .unwrap_or_else(|error| panic!("read real artifact {relative}: {error}"))
}

/// THE regression test for the reported hole.
#[test]
fn substituted_empty_garbage_and_failed_artifacts_are_never_present_evidence() {
    for artifact in SUBSTITUTION_TARGETS {
        let tree = EvidenceTree::new("core");

        // Control: the real committed content must still be accepted, or the
        // arms below would prove nothing but that the gate rejects everything.
        tree.write(artifact, &real_artifact(artifact));
        assert_eq!(
            tree.state_of(artifact),
            EvidenceState::Present,
            "the real committed {artifact} must remain valid evidence"
        );

        // Arm 1 — a ZERO-BYTE file. Measured `present` before this fix.
        tree.write(artifact, "");
        assert_ne!(
            tree.state_of(artifact),
            EvidenceState::Present,
            "a zero-byte {artifact} must not back a row"
        );

        // Arm 2 — non-JSON garbage. Measured `present` before this fix.
        tree.write(artifact, "this is not json at all, it is prose\n");
        assert_ne!(
            tree.state_of(artifact),
            EvidenceState::Present,
            "non-JSON garbage in {artifact} must not back a row"
        );

        // Arm 3 — JSON reporting its OWN failure. Measured `present` before
        // this fix: the gate accepted an artifact that said it had failed.
        tree.write(artifact, "{\"status\":\"FAILED\"}\n");
        assert_ne!(
            tree.state_of(artifact),
            EvidenceState::Present,
            "{artifact} reporting status=FAILED must not back a row"
        );

        // Arm 4 — valid JSON, right shape, WRONG artifact. A well-formed report
        // from a different gate is not this row's evidence.
        tree.write(
            artifact,
            "{\"schema_version\":\"clean-some-other-report-v1\",\"status\":\"passed\"}\n",
        );
        assert_ne!(
            tree.state_of(artifact),
            EvidenceState::Present,
            "a foreign schema_version in {artifact} must not back a row"
        );

        // Arm 5 — the real content again, proving the tree itself is not stuck.
        tree.write(artifact, &real_artifact(artifact));
        assert_eq!(
            tree.state_of(artifact),
            EvidenceState::Present,
            "{artifact} must recover once real evidence is restored"
        );
    }
}

/// A failed artifact must move the ROW, not merely the classification.
#[test]
fn invalid_evidence_downgrades_a_declared_green_row() {
    assert_eq!(
        effective_status_for(ReplacementStatus::Green, EvidenceState::Invalid),
        ReplacementStatus::PendingEvidence,
        "a Green row whose evidence fails its contract must not stay Green"
    );
    // The sound behaviour that already existed must not regress.
    for state in [EvidenceState::Missing, EvidenceState::Stub] {
        assert_eq!(
            effective_status_for(ReplacementStatus::Green, state),
            ReplacementStatus::PendingEvidence,
            "{state:?} evidence must keep downgrading a declared Green"
        );
    }
    assert_eq!(
        effective_status_for(ReplacementStatus::Green, EvidenceState::Present),
        ReplacementStatus::Green,
        "validated evidence must still be able to back a Green row"
    );
}

/// The cwd-first resolution hole: three EMPTY files in a foreign directory
/// scored three rows green. Resolution is now anchored to one recorded root.
#[test]
fn evidence_never_resolves_against_a_foreign_working_directory() {
    let foreign = EvidenceTree::new("foreign");
    for artifact in SUBSTITUTION_TARGETS {
        foreign.write(artifact, "");
    }
    for artifact in SUBSTITUTION_TARGETS {
        assert_ne!(
            foreign.state_of(artifact),
            EvidenceState::Present,
            "an empty {artifact} in a foreign tree must never score present"
        );
    }

    // And the resolver anchors to a root it names, never to a bare relative
    // path that the process working directory could reinterpret.
    let (root, source) = repo_root_provenance();
    assert!(
        root.is_absolute() || source == RepoRootSource::WorkingDirectoryFallback,
        "the evidence root must be an absolute, recorded location (got {root:?} via {source:?})"
    );
    assert_eq!(
        repo_artifact_path("reports/compile-runtime-smoke.json"),
        root.join("reports/compile-runtime-smoke.json"),
        "declared artifacts must resolve under the recorded root, not the cwd"
    );
}

/// Provenance must be in the OUTPUT, not merely in the resolver: a reader has
/// to be able to tell which file on which tree produced each verdict.
#[test]
fn informational_scorecard_records_where_every_artifact_resolved() {
    let scorecard = InformationalScorecard::current();
    assert!(
        !scorecard.evidence_root.is_empty(),
        "the scorecard must name the tree it scored"
    );
    assert!(
        !scorecard.evidence_root_source.is_empty(),
        "the scorecard must say on whose authority that root was chosen"
    );
    for row in &scorecard.rows {
        if row.evidence_state == EvidenceState::SchemaName {
            continue;
        }
        assert!(
            !row.evidence_artifacts.is_empty(),
            "row {} scored {:?} with no recorded artifact provenance",
            row.id,
            row.evidence_state
        );
        for artifact in &row.evidence_artifacts {
            assert!(
                artifact.resolved_path.ends_with(&artifact.declared),
                "row {} resolved {} to {}, which is not that artifact",
                row.id,
                artifact.declared,
                artifact.resolved_path
            );
            assert_eq!(
                artifact.detail.is_none(),
                artifact.state == EvidenceState::Present,
                "row {} must explain exactly the artifacts it refuses ({})",
                row.id,
                artifact.declared
            );
        }
    }
}

/// Every declared evidence path must have a contract, or the fail-closed
/// default silently turns a real row INVALID and nobody learns why.
#[test]
fn every_replacement_row_artifact_has_a_declared_contract() {
    for row in replacement_rows() {
        if !row.evidence_artifact.contains('/') {
            continue; // schema-name evidence, validated by the gate command
        }
        for declared in row.evidence_artifact.split(';') {
            let declared = declared.trim();
            if declared.is_empty() || !declared.contains('/') {
                continue;
            }
            assert!(
                evidence_contract_for(declared).is_some(),
                "row {} declares {declared} as evidence with no contract in \
                 evidence_contract_for; add one (this default is fail-closed)",
                row.id
            );
        }
    }
}

/// The two notions of validity must AGREE. `clean replacement validate-report`
/// pins each report kind's schema; the evidence contract must pin the same one,
/// or the gate and the validator can disagree about the same file.
#[test]
fn evidence_contract_agrees_with_validate_report_kinds() {
    for (kind, artifact) in [
        (
            ReplacementReportKind::NativeLibrary,
            "reports/native-library-replacement.json",
        ),
        (
            ReplacementReportKind::MathverseReplay,
            "reports/mathverse-replay-replacement.json",
        ),
        (
            ReplacementReportKind::LspInfoview,
            "reports/lsp-infoview-parity.json",
        ),
        (
            ReplacementReportKind::FrontendParity,
            "tests/lean4_compat/frontend_replacement_scorecard.json",
        ),
    ] {
        let contract = evidence_contract_for(artifact)
            .unwrap_or_else(|| panic!("{artifact} has no declared evidence contract"));
        // `Unproduced` (the LSP report since 2026-09-25) validates real content
        // exactly as `JsonReport` does, so it must pin the same schema too.
        let Some(schema_version) = contract.json_schema() else {
            panic!("{artifact} is a validate-report kind and must carry a JSON contract");
        };
        assert_eq!(
            schema_version,
            kind.expected_schema(),
            "evidence contract and validate-report disagree about {artifact}"
        );
    }
}

/// An artifact whose path nobody declared is not evidence. This is the property
/// that keeps a newly-added row from scoring green off an unreviewed file.
#[test]
fn an_undeclared_artifact_path_is_refused() {
    let tree = EvidenceTree::new("undeclared");
    tree.write(
        "reports/not-a-declared-artifact.json",
        "{\"schema_version\":\"clean-anything-v1\",\"status\":\"passed\"}\n",
    );
    assert_eq!(
        tree.state_of("reports/not-a-declared-artifact.json"),
        EvidenceState::Invalid,
        "a perfectly well-formed report at an undeclared path is still not evidence"
    );
}

/// Fail-closed combination across a semicolon list, and the stub path that
/// already worked must keep working.
#[test]
fn multi_path_evidence_combines_fail_closed() {
    let tree = EvidenceTree::new("multi");
    tree.write("docs/RELEASE_READINESS.md", "# Release readiness\n\nreal\n");
    tree.write("docs/SOUNDNESS_CERTIFICATE.md", "# Soundness\n\nreal\n");
    assert_eq!(
        tree.state_of("docs/RELEASE_READINESS.md; docs/SOUNDNESS_CERTIFICATE.md"),
        EvidenceState::Present,
        "two satisfied document contracts back the row"
    );

    // One blank sibling condemns the list — a present neighbour must not mask it.
    tree.write("docs/SOUNDNESS_CERTIFICATE.md", "   \n\n");
    assert_eq!(
        tree.state_of("docs/RELEASE_READINESS.md; docs/SOUNDNESS_CERTIFICATE.md"),
        EvidenceState::Invalid,
        "a blank document must not be masked by a present sibling"
    );

    // A missing sibling still outranks everything.
    fs::remove_file(tree.root.join("docs/SOUNDNESS_CERTIFICATE.md")).expect("remove");
    assert_eq!(
        tree.state_of("docs/RELEASE_READINESS.md; docs/SOUNDNESS_CERTIFICATE.md"),
        EvidenceState::Missing,
        "a missing path must not be masked by a present sibling"
    );

    // The `{"stub": true}` placeholder classification must not regress. (This
    // used the LSP report until 2026-09-25; that path is `Unproduced` now and
    // its stub reads VACUOUS -- slice 20 pins that. A path with an ordinary
    // JSON contract keeps the plain Stub reading.)
    tree.write(
        "reports/native-library-replacement.json",
        "{\"stub\": true}\n",
    );
    assert_eq!(
        tree.state_of("reports/native-library-replacement.json"),
        EvidenceState::Stub,
        "a stub must still classify as Stub, not merely Invalid"
    );
}

/// `validate_evidence_artifact` is the shared notion of validity; pin the exact
/// reasons so a future edit cannot quietly widen what counts.
#[test]
fn json_evidence_validation_names_its_reason() {
    let artifact = "reports/compile-runtime-smoke.json";
    let expect_err = |contents: &str, needle: &str| {
        let error = validate_evidence_artifact(artifact, contents).expect_err("must refuse");
        assert!(
            error.contains(needle),
            "expected refusal mentioning {needle:?}, got {error:?}"
        );
    };
    expect_err("", "not valid JSON");
    expect_err("garbage", "not valid JSON");
    expect_err("[1, 2, 3]", "not a JSON object");
    expect_err("{}", "schema_version expected");
    expect_err(
        "{\"schema_version\":\"clean-compile-runtime-smoke-v1\",\"status\":\"failed\"}",
        "reports its own failure",
    );
    expect_err(
        "{\"schema_version\":\"clean-compile-runtime-smoke-v1\",\"passed\":false}",
        "reports its own failure",
    );
    // An honest in-progress artifact is NOT a failure: `launch_ready: false` is
    // the shape every non-green report is supposed to have.
    validate_evidence_artifact(
        artifact,
        "{\"schema_version\":\"clean-compile-runtime-smoke-v1\",\"launch_ready\":false}",
    )
    .expect("launch_ready=false is honesty, not failure");
}

/// The integer-`schema_version` artifact must compare by value, not by Rust
/// type, or the benchmark publication evidence silently goes INVALID.
#[test]
fn integer_schema_versions_compare_by_value() {
    let artifact = "reports/benchmarks/publication/current.json";
    validate_evidence_artifact(artifact, "{\"schema_version\":1,\"status\":\"published\"}")
        .expect("an integer schema_version of 1 satisfies the pin");
    validate_evidence_artifact(
        artifact,
        "{\"schema_version\":\"1\",\"status\":\"published\"}",
    )
    .expect("a string schema_version of \"1\" satisfies the same pin");
    assert!(
        validate_evidence_artifact(artifact, "{\"schema_version\":2}").is_err(),
        "a different schema_version must still be refused"
    );
}
