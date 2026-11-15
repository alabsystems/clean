// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! No Green on vacuous evidence (slice 20, roadmap Phase 0 package P0_NET).
//!
//! THE DEFECT (measured 2026-09-24 against the release binary, then re-measured
//! at 5c83a2f3d before this change): `clean replacement status --informational`
//! scored `tactic-parity` GREEN off `reports/tactic-parity-counts.json`, whose 56
//! rows all read `"matched": true` because `matched: true` is a LITERAL in the
//! production source that generates them, and whose `lean4_fixture` values are
//! label strings -- pinned Lean is never run. The file satisfied its old JSON
//! contract perfectly; the contract asked the wrong question. The row now reads
//! `unknown`, with a detail line naming what would mint real evidence.
//!
//! `lsp-infoview`, measured rather than assumed: it was never Green -- it is
//! declared `PendingEvidence` and `effective_status_for` never upgrades -- so
//! the "Green on a stub" half of the audit finding does not reproduce for it.
//! What does reproduce is the vacuity: its artifact is the `{"stub": true}`
//! placeholder and NO command in the tree writes a `clean-lsp-infoview-parity-v1`
//! report (the schema appears only in two validators), so "pending evidence"
//! promised something nothing can mint. Its contract is
//! `EvidenceContract::Unproduced`: the placeholder reads `unknown` with the
//! producer named, and a real report would be validated as before.
//! `compile-runtime` belongs to package P0_EXEC and is not touched here.
//!
//! Every arm is two-way: a control that must stay `Present` / `Green` sits
//! beside each refusal, so the slice cannot pass against a scorecard that says
//! no to everything.

use crate::cmd_replacement::*;

const TACTIC_COUNTS: &str = "reports/tactic-parity-counts.json";
/// A sibling artifact of the same shape that is NOT vacuous: the control.
const CONTROL: &str = "reports/strict-solver-fragment-dashboard.json";

fn scratch_root(tag: &str) -> tempfile::TempDir {
    tempfile::Builder::new()
        .prefix(&format!("clean-vacuous-evidence-{tag}-"))
        .tempdir()
        .expect("tempdir")
}

fn plant(root: &Path, relative: &str, contents: &str) {
    let path = root.join(relative);
    fs::create_dir_all(path.parent().expect("artifact parent")).expect("mkdir");
    fs::write(path, contents).expect("write artifact");
}

fn real_artifact(relative: &str) -> String {
    fs::read_to_string(repo_artifact_path(relative))
        .unwrap_or_else(|error| panic!("read real artifact {relative}: {error}"))
}

/// Whatever sits at the vacuous path -- the committed file, a report shaped
/// exactly like a passing one, or nothing -- it can never back a row.
#[test]
fn test_evidence_tactic_parity_counts_is_vacuous_whatever_it_contains() {
    let dir = scratch_root("contents");
    let root = dir.path();
    let state = |root: &Path| assess_evidence_in_root(root, TACTIC_COUNTS).state;

    plant(root, TACTIC_COUNTS, &real_artifact(TACTIC_COUNTS));
    assert_eq!(
        state(root),
        EvidenceState::Vacuous,
        "the committed artifact"
    );
    plant(
        root,
        TACTIC_COUNTS,
        "{\"schema_version\":\"clean-tactic-parity-count-artifact-v1\",\"status\":\"passed\"}\n",
    );
    assert_eq!(
        state(root),
        EvidenceState::Vacuous,
        "a perfectly shaped passing report"
    );
    fs::remove_file(root.join(TACTIC_COUNTS)).expect("remove");
    assert_eq!(state(root), EvidenceState::Vacuous, "no file at all");

    // Control: the non-vacuous sibling still backs its row with its real bytes.
    plant(root, CONTROL, &real_artifact(CONTROL));
    assert_eq!(
        assess_evidence_in_root(root, CONTROL).state,
        EvidenceState::Present,
        "a real, non-vacuous artifact must still score present"
    );
}

/// The detail is the actionable half: it must say what the artifact is and
/// what would replace it.
#[test]
fn test_evidence_vacuous_detail_names_what_would_mint_real_evidence() {
    let dir = scratch_root("detail");
    let assessment = assess_evidence_in_root(dir.path(), TACTIC_COUNTS);
    let detail = assessment.artifacts[0]
        .detail
        .as_deref()
        .expect("a vacuous artifact carries a detail");
    for needle in [
        "VACUOUS",
        "matched: true",
        "pinned Lean",
        "real evidence would be",
    ] {
        assert!(
            detail.contains(needle),
            "detail {detail:?} does not mention {needle:?}"
        );
    }
    let error = validate_evidence_artifact(TACTIC_COUNTS, &real_artifact(TACTIC_COUNTS))
        .expect_err("the shared validity notion must refuse a vacuous path too");
    assert_eq!(
        error, detail,
        "the gate and the validator must give ONE reason"
    );
}

/// VACUOUS reads UNKNOWN for every declared status but `Blocked`, and never
/// moves a non-vacuous verdict.
#[test]
fn test_effective_status_vacuous_evidence_reads_unknown_never_green() {
    for declared in [
        ReplacementStatus::Green,
        ReplacementStatus::InProgress,
        ReplacementStatus::PendingEvidence,
    ] {
        assert_eq!(
            effective_status_for(declared, EvidenceState::Vacuous),
            ReplacementStatus::Unknown,
            "a declared {declared:?} on vacuous evidence"
        );
    }
    assert_eq!(
        effective_status_for(ReplacementStatus::Blocked, EvidenceState::Vacuous),
        ReplacementStatus::Blocked,
        "a known blocker stays a known blocker"
    );
    assert_eq!(
        effective_status_for(ReplacementStatus::Green, EvidenceState::Present),
        ReplacementStatus::Green,
        "control: present evidence still backs a declared Green"
    );
}

/// The row itself, end to end through the scorecard a user runs.
#[test]
fn test_informational_tactic_parity_row_is_unknown_not_green() {
    let row = replacement_rows()
        .into_iter()
        .find(|row| row.id == "tactic-parity")
        .expect("tactic-parity row");
    assert_eq!(
        row.status,
        ReplacementStatus::Green,
        "the DECLARATION is unchanged"
    );
    assert_eq!(row.evidence_state, EvidenceState::Vacuous);
    assert_eq!(row.effective_status, ReplacementStatus::Unknown);

    let scorecard = InformationalScorecard::current();
    let informational = scorecard
        .rows
        .iter()
        .find(|row| row.id == "tactic-parity")
        .expect("informational tactic-parity row");
    assert_eq!(informational.effective_status, ReplacementStatus::Unknown);
    let mut buf = Vec::new();
    render_informational_human(&mut buf, &scorecard).expect("render");
    let text = String::from_utf8(buf).expect("utf8");
    let line = text
        .lines()
        .find(|line| line.trim_start().starts_with("tactic-parity "))
        .expect("tactic-parity line");
    assert!(
        line.contains("unknown") && line.contains("VACUOUS"),
        "{line}"
    );
    assert!(!line.contains("green"), "{line}");
    assert!(
        text.contains("real evidence would be"),
        "the detail line must be printed"
    );

    // Control: the non-vacuous sibling row is not swept up with it.
    let strict = scorecard
        .rows
        .iter()
        .find(|row| row.id == "strict-reconstruction")
        .expect("strict-reconstruction row");
    assert_ne!(strict.evidence_state, EvidenceState::Vacuous);
}

/// The general property, over every row: no Green rests on vacuous evidence.
#[test]
fn test_informational_no_green_row_rests_on_vacuous_evidence() {
    let scorecard = InformationalScorecard::current();
    let vacuous: Vec<_> = scorecard
        .rows
        .iter()
        .filter(|row| row.evidence_state == EvidenceState::Vacuous)
        .collect();
    assert!(
        !vacuous.is_empty(),
        "vacuous: the property must have a subject"
    );
    for row in vacuous {
        assert_ne!(
            row.effective_status,
            ReplacementStatus::Green,
            "row {}",
            row.id
        );
    }
}

/// UNKNOWN is launch-blocking and has its own bucket, so the non-green buckets
/// still partition the non-green rows.
#[test]
fn test_readiness_unknown_rows_block_launch_in_their_own_bucket() {
    let rows = replacement_rows();
    let tooling = rust_first_tooling_status();
    let accounting =
        ReplacementReadinessAccounting::from_current(&rows, &tooling, true, false, false);
    assert!(accounting
        .launch_blocking_row_ids
        .contains(&"tactic-parity"));
    assert!(accounting.unknown_required_row_count >= 1);
    assert_eq!(
        accounting.non_green_required_row_count,
        accounting.blocked_required_row_count
            + accounting.pending_evidence_required_row_count
            + accounting.in_progress_required_row_count
            + accounting.unknown_required_row_count
    );
}

const LSP_PARITY: &str = "reports/lsp-infoview-parity.json";

/// The LSP placeholder is VACUOUS, but the PATH is not: a real report is
/// validated exactly as before, so minting one needs no contract change.
#[test]
fn test_evidence_lsp_infoview_stub_is_vacuous_but_a_real_report_still_validates() {
    let dir = scratch_root("lsp");
    let root = dir.path();
    let state = |root: &Path| assess_evidence_in_root(root, LSP_PARITY).state;

    plant(root, LSP_PARITY, &real_artifact(LSP_PARITY));
    assert_eq!(
        state(root),
        EvidenceState::Vacuous,
        "the committed placeholder"
    );
    let assessment = assess_evidence_in_root(root, LSP_PARITY);
    let detail = assessment.artifacts[0].detail.as_deref().expect("detail");
    for needle in [
        "VACUOUS",
        "no command in the tree produces a clean-lsp-infoview-parity-v1 report",
        "real evidence would be",
        "clean lsp",
    ] {
        assert!(
            detail.contains(needle),
            "detail {detail:?} does not mention {needle:?}"
        );
    }
    let error = validate_evidence_artifact(LSP_PARITY, &real_artifact(LSP_PARITY))
        .expect_err("the validator must refuse the placeholder too");
    assert_eq!(
        error, detail,
        "the gate and the validator must give ONE reason"
    );

    // Controls, both directions: a real report with the pinned schema backs
    // the row, a report with the wrong schema is Invalid, and no file at all
    // is Missing -- the vacuity is the placeholder's, never the path's.
    plant(
        root,
        LSP_PARITY,
        "{\"schema_version\":\"clean-lsp-infoview-parity-v1\",\"status\":\"passed\"}\n",
    );
    assert_eq!(
        state(root),
        EvidenceState::Present,
        "a real report backs the row"
    );
    plant(
        root,
        LSP_PARITY,
        "{\"schema_version\":\"clean-lsp-infoview-parity-v0\"}\n",
    );
    assert_eq!(
        state(root),
        EvidenceState::Invalid,
        "a wrong schema is refused"
    );
    fs::remove_file(root.join(LSP_PARITY)).expect("remove");
    assert_eq!(
        state(root),
        EvidenceState::Missing,
        "no file is Missing, not Vacuous"
    );
}

/// The row end to end: `unknown`, never `pending_evidence`, with the producer
/// that would mint real evidence printed on its detail line.
#[test]
fn test_informational_lsp_infoview_row_is_unknown_naming_its_producer() {
    let row = replacement_rows()
        .into_iter()
        .find(|row| row.id == "lsp-infoview")
        .expect("lsp-infoview row");
    assert_eq!(
        row.status,
        ReplacementStatus::PendingEvidence,
        "the DECLARATION is unchanged"
    );
    assert_eq!(row.evidence_state, EvidenceState::Vacuous);
    assert_eq!(row.effective_status, ReplacementStatus::Unknown);

    let scorecard = InformationalScorecard::current();
    let mut buf = Vec::new();
    render_informational_human(&mut buf, &scorecard).expect("render");
    let text = String::from_utf8(buf).expect("utf8");
    let line = text
        .lines()
        .find(|line| line.trim_start().starts_with("lsp-infoview "))
        .expect("lsp-infoview line");
    assert!(
        line.contains("unknown") && line.contains("VACUOUS"),
        "{line}"
    );
    assert!(!line.contains("pending_evidence"), "{line}");
    assert!(
        text.contains("no command in the tree produces a clean-lsp-infoview-parity-v1 report"),
        "the detail line must say why"
    );

    // Control: a stub under an ordinary JSON contract keeps its Stub reading
    // and its declared status -- `Unproduced` is not a blanket over stubs.
    let native = scorecard
        .rows
        .iter()
        .find(|row| row.id == "native-libraries")
        .expect("native-libraries row");
    assert_eq!(native.evidence_state, EvidenceState::Stub);
    assert_eq!(native.effective_status, native.declared_status);
}

/// A zero-trust gate's `pending_evidence` verdict moves a row toward LESS
/// confidence and never rewrites `unknown`: that would trade the VACUOUS
/// reason for a word promising evidence nothing can mint.
#[test]
fn test_reconcile_with_gate_verdict_pending_gate_keeps_unknown() {
    assert_eq!(
        reconcile_with_gate_verdict(
            ReplacementStatus::Unknown,
            Some(ZeroTrustGateStatus::PendingEvidence)
        ),
        ReplacementStatus::Unknown
    );
    assert_eq!(
        reconcile_with_gate_verdict(
            ReplacementStatus::Unknown,
            Some(ZeroTrustGateStatus::Blocked)
        ),
        ReplacementStatus::Blocked,
        "a blocked gate still wins"
    );
    assert_eq!(
        reconcile_with_gate_verdict(
            ReplacementStatus::Green,
            Some(ZeroTrustGateStatus::PendingEvidence)
        ),
        ReplacementStatus::PendingEvidence,
        "control: a pending gate still demotes a Green"
    );
}
