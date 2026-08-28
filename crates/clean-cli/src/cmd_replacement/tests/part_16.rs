// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests (slice 16) for the row prose that lives in `data/`, not in code.
//!
//! `sha256_repo_module_tree` pins every non-test `.rs` file under
//! `cmd_replacement/` into `reports/kernel-soundness-launch-evidence.json`, so
//! before `data/replacement_row_prose.json` existed a one-word fix to a stale
//! sentence flipped the `kernel-differential` row Green -> PendingEvidence and
//! demanded a full re-mint. Moving the prose out is only safe while two things
//! hold, and both are measured here rather than asserted:
//!
//! 1. every row still HAS its prose (nothing silently renders empty), and
//! 2. the prose is INERT — no launch-gate decision reads it.
//!
//! (2) is the load-bearing one. It is checked by mutation: scramble every
//! `blocker` and `removal_condition`, rebuild the readiness accounting, and
//! require every decision it makes to be byte-identical. A future predicate on
//! either field turns this red instead of quietly widening the digest boundary.

use crate::cmd_replacement::*;

const SCRAMBLED: &str = "SCRAMBLED PROSE — if this text can change a verdict, the digest boundary \
                         at REPLACEMENT_ROW_PROSE_PATH is wrong.";

#[test]
fn row_prose_covers_every_row_and_has_no_orphans() {
    let prose = row_prose();

    let declared_row_ids: Vec<&str> = replacement_rows().iter().map(|row| row.id).collect();
    let missing: Vec<&str> = declared_row_ids
        .iter()
        .copied()
        .filter(|id| replacement_row_blocker(id) == MISSING_ROW_PROSE)
        .collect();
    assert!(
        missing.is_empty(),
        "replacement rows with no entry in {REPLACEMENT_ROW_PROSE_PATH}: {missing:?}"
    );

    let declared_tool_ids: Vec<&str> = python_tool_migration_rows()
        .iter()
        .map(|row| row.id)
        .collect();
    let missing_tools: Vec<&str> = declared_tool_ids
        .iter()
        .copied()
        .filter(|id| python_tool_row_prose(id).1 == MISSING_ROW_PROSE)
        .collect();
    assert!(
        missing_tools.is_empty(),
        "python tool rows with no entry in {REPLACEMENT_ROW_PROSE_PATH}: {missing_tools:?}"
    );

    // Orphans are the other half: prose for a row that no longer exists is prose
    // nobody will ever read, and it is how a stale sentence outlives its row.
    let orphan_rows: Vec<&str> = prose
        .replacement_row_ids()
        .into_iter()
        .filter(|id| !declared_row_ids.contains(id))
        .collect();
    assert!(
        orphan_rows.is_empty(),
        "{REPLACEMENT_ROW_PROSE_PATH} has replacement_rows prose for rows that do not exist: {orphan_rows:?}"
    );
    let orphan_tools: Vec<&str> = prose
        .python_tool_row_ids()
        .into_iter()
        .filter(|id| !declared_tool_ids.contains(id))
        .collect();
    assert!(
        orphan_tools.is_empty(),
        "{REPLACEMENT_ROW_PROSE_PATH} has python_tool_rows prose for rows that do not exist: {orphan_tools:?}"
    );
}

/// The digest boundary, proved by mutation rather than claimed.
///
/// Scrambling every prose field must leave every launch-gate decision
/// bit-identical. If it does not, prose is behaviour and belongs back inside
/// the digested source tree.
#[test]
fn row_prose_is_inert_for_every_launch_gate_decision() {
    let rows = replacement_rows();
    let tooling = rust_first_tooling_status();

    let mut scrambled_rows = replacement_rows();
    for row in &mut scrambled_rows {
        row.blocker = SCRAMBLED;
    }
    let mut scrambled_tooling = rust_first_tooling_status();
    for command in &mut scrambled_tooling.commands {
        command.blocker = SCRAMBLED;
        command.removal_condition = SCRAMBLED;
    }

    // Guard against a vacuous pass: the mutation must actually have landed.
    assert_ne!(
        rows.first().map(|row| row.blocker),
        scrambled_rows.first().map(|row| row.blocker),
        "the scramble did not change anything, so this test proves nothing"
    );
    assert_ne!(
        tooling.commands.first().map(|row| row.blocker),
        scrambled_tooling.commands.first().map(|row| row.blocker),
        "the scramble did not change anything, so this test proves nothing"
    );

    let baseline =
        ReplacementReadinessAccounting::from_current(&rows, &tooling, true, false, false);
    let mutated = ReplacementReadinessAccounting::from_current(
        &scrambled_rows,
        &scrambled_tooling,
        true,
        false,
        false,
    );

    assert_eq!(baseline.required_row_count, mutated.required_row_count);
    assert_eq!(
        baseline.green_required_row_count,
        mutated.green_required_row_count
    );
    assert_eq!(
        baseline.non_green_required_row_count,
        mutated.non_green_required_row_count
    );
    assert_eq!(
        baseline.blocked_required_row_count,
        mutated.blocked_required_row_count
    );
    assert_eq!(
        baseline.pending_evidence_required_row_count,
        mutated.pending_evidence_required_row_count
    );
    assert_eq!(
        baseline.in_progress_required_row_count,
        mutated.in_progress_required_row_count
    );
    assert_eq!(
        baseline.launch_blocking_row_ids,
        mutated.launch_blocking_row_ids
    );
    assert_eq!(
        baseline.rust_first_launch_blocking_command_ids,
        mutated.rust_first_launch_blocking_command_ids
    );
    assert_eq!(baseline.python_wrapper_count, mutated.python_wrapper_count);
    assert_eq!(
        baseline.launch_blocking_python_wrapper_count,
        mutated.launch_blocking_python_wrapper_count
    );
    assert_eq!(
        baseline.replacement_critical_python_wrapper_count,
        mutated.replacement_critical_python_wrapper_count
    );
    assert_eq!(
        baseline.certification_python_dependency_ids,
        mutated.certification_python_dependency_ids
    );
    assert_eq!(
        baseline.non_launch_python_reference_ids,
        mutated.non_launch_python_reference_ids
    );
    assert_eq!(
        baseline.replacement_row_proof_surface_audit.status,
        mutated.replacement_row_proof_surface_audit.status
    );
    assert_eq!(
        baseline
            .replacement_row_proof_surface_audit
            .wrapper_gate_row_ids,
        mutated
            .replacement_row_proof_surface_audit
            .wrapper_gate_row_ids
    );
    // The reviewer deck fingerprint is a sha256 over the reviewer-visible proof
    // commands; if prose ever leaked into it, this single line catches it.
    assert_eq!(
        baseline.reviewer_proof_command_deck.fingerprint_sha256,
        mutated.reviewer_proof_command_deck.fingerprint_sha256
    );
    assert_eq!(
        baseline
            .certification_wrapper_free_gate
            .wrapper_dependency_blocker_ids,
        mutated
            .certification_wrapper_free_gate
            .wrapper_dependency_blocker_ids
    );
    assert_eq!(
        baseline.full_replacement_certification_gate.launch_ready,
        mutated.full_replacement_certification_gate.launch_ready
    );
    assert_eq!(
        baseline.blocker_evidence_requirements.len(),
        mutated.blocker_evidence_requirements.len()
    );

    // The tooling verdict itself must also be prose-independent.
    assert_eq!(tooling.launch_ready, scrambled_tooling.launch_ready);
    assert_eq!(tooling.overall_status, scrambled_tooling.overall_status);
    assert_eq!(tooling.counts, scrambled_tooling.counts);
}

/// DIRECTION 2 of the inertness proof: the comparison must still be able to
/// say no.
///
/// `row_prose_is_inert_for_every_launch_gate_decision` passes because nothing
/// moved. A comparison that can never move passes for the same reason and
/// proves nothing — that is this repo's own definition of a worthless gate. So
/// here the same comparison is handed a change to a field that IS behaviour
/// (`status`), and is required to notice. If this arm ever goes green, the
/// inertness test above has stopped being evidence.
#[test]
fn row_prose_inertness_comparison_still_detects_a_real_change() {
    let tooling = rust_first_tooling_status();
    let rows = replacement_rows();

    let mut behavioural_change = replacement_rows();
    for row in &mut behavioural_change {
        // Not prose: this is the field the launch gate counts.
        row.effective_status = ReplacementStatus::Green;
    }

    let baseline =
        ReplacementReadinessAccounting::from_current(&rows, &tooling, true, false, false);
    let changed = ReplacementReadinessAccounting::from_current(
        &behavioural_change,
        &tooling,
        true,
        false,
        false,
    );

    assert_ne!(
        baseline.green_required_row_count, changed.green_required_row_count,
        "the inertness comparison cannot detect a real change, so it proves nothing"
    );
    assert_ne!(
        baseline.launch_blocking_row_ids, changed.launch_blocking_row_ids,
        "the inertness comparison cannot detect a real change, so it proves nothing"
    );
}

/// A row's reconciled status must be a function of its non-prose fields alone.
#[test]
fn effective_status_is_derived_only_from_non_prose_fields() {
    for row in replacement_rows() {
        assert_eq!(
            row.evidence_state,
            evidence_state_of(row.evidence_artifact),
            "row {} evidence_state is not a function of evidence_artifact",
            row.id
        );
        assert_eq!(
            row.effective_status,
            effective_status_for(row.status, row.evidence_state),
            "row {} effective_status is not a function of (status, evidence_state)",
            row.id
        );
    }
}
