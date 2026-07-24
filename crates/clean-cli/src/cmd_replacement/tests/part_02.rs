// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests (slice 2) for the `clean replacement` command group,
//! split from the original single-file `cmd_replacement.rs` tests module.

use super::support::*;
use crate::cmd_replacement::*;

#[test]
fn replacement_status_accounts_launch_blockers_without_green_claims() {
    let Ok(report) = ReplacementStatusReport::current() else {
        eprintln!("SKIP: replacement status report artifacts not present on this machine");
        return;
    };
    let accounting = &report.readiness_accounting;
    let required_rows: Vec<_> = report
        .rows
        .iter()
        .filter(|row| row.required_for_launch)
        .collect();

    assert_eq!(accounting.required_row_count, required_rows.len());
    assert_eq!(
        accounting.green_required_row_count,
        required_rows
            .iter()
            .filter(|row| row.status == ReplacementStatus::Green)
            .count()
    );
    assert_eq!(
        accounting.non_green_required_row_count,
        accounting.launch_blocking_row_ids.len()
    );
    assert_eq!(
        accounting.non_green_required_row_count,
        accounting.blocked_required_row_count
            + accounting.pending_evidence_required_row_count
            + accounting.in_progress_required_row_count
    );
    assert!(accounting
        .launch_blocking_row_ids
        .contains(&"rust-first-tooling"));
    assert!(accounting.launch_blocking_row_ids.contains(&"launch-docs"));
    assert!(!accounting
        .rust_first_launch_blocking_command_ids
        .contains(&"benchmark-publication-launch"));
    assert!(!accounting
        .rust_first_launch_blocking_command_ids
        .contains(&"release-issue-hygiene"));
    assert!(!accounting
        .rust_first_launch_blocking_command_ids
        .contains(&"trust-boundary-audit-report"));
    assert_eq!(
        accounting.non_green_required_row_count,
        accounting.blocker_evidence_requirements.len()
    );
    assert_eq!(
        accounting.replacement_row_proof_surface_audit.status,
        "passed"
    );
    assert_eq!(
        accounting
            .replacement_row_proof_surface_audit
            .checked_row_count,
        report.rows.len()
    );
    assert_eq!(
        accounting
            .replacement_row_proof_surface_audit
            .wrapper_gate_row_count,
        0
    );
    assert!(accounting
        .replacement_row_proof_surface_audit
        .wrapper_gate_row_ids
        .is_empty());
    assert_eq!(
        accounting
            .replacement_row_proof_surface_audit
            .wrapper_evidence_artifact_row_count,
        0
    );
    assert!(accounting
        .replacement_row_proof_surface_audit
        .wrapper_evidence_artifact_row_ids
        .is_empty());
    assert!(accounting
        .replacement_row_proof_surface_audit
        .reviewer_rule
        .contains("must not require python3"));
    assert_eq!(
        accounting.reviewer_proof_command_deck.command_count,
        report.rows.len()
    );
    assert_eq!(
        accounting
            .reviewer_proof_command_deck
            .wrapper_free_command_count,
        report.rows.len()
    );
    assert_eq!(
        accounting
            .reviewer_proof_command_deck
            .wrapper_dependent_command_count,
        0
    );
    assert!(accounting
        .reviewer_proof_command_deck
        .wrapper_dependent_row_ids
        .is_empty());
    assert_eq!(
        accounting
            .reviewer_proof_command_deck
            .launch_blocking_command_count,
        accounting.non_green_required_row_count
    );
    assert_eq!(
        accounting
            .reviewer_proof_command_deck
            .launch_blocking_row_ids,
        accounting.launch_blocking_row_ids
    );
    assert_eq!(
        accounting
            .reviewer_proof_command_deck
            .launch_blocking_wrapper_free_command_count,
        accounting.non_green_required_row_count
    );
    assert_eq!(
        accounting
            .reviewer_proof_command_deck
            .launch_blocking_wrapper_dependent_command_count,
        0
    );
    assert!(accounting
        .reviewer_proof_command_deck
        .launch_blocking_wrapper_dependent_row_ids
        .is_empty());
    assert_eq!(
        accounting
            .reviewer_proof_command_deck
            .launch_blocking_commands
            .len(),
        accounting.non_green_required_row_count
    );
    assert_eq!(
        accounting
            .reviewer_proof_command_deck
            .launch_blocking_commands
            .iter()
            .map(|command| command.row_id)
            .collect::<Vec<_>>(),
        accounting.launch_blocking_row_ids
    );
    assert!(accounting
        .reviewer_proof_command_deck
        .launch_blocking_commands
        .iter()
        .all(|command| command.wrapper_free && command.launch_blocking_until_green));
    assert_eq!(accounting.certification_wrapper_free_gate.status, "passed");
    assert_eq!(
        accounting
            .certification_wrapper_free_gate
            .certifying_python_dependency_count,
        accounting.certification_python_dependency_count
    );
    assert_eq!(
        accounting
            .certification_wrapper_free_gate
            .wrapper_dependent_proof_surface_count,
        0
    );
    assert_eq!(
        accounting
            .certification_wrapper_free_gate
            .wrapper_dependent_command_count,
        accounting
            .reviewer_proof_command_deck
            .wrapper_dependent_command_count
    );
    assert_eq!(
        accounting
            .certification_wrapper_free_gate
            .launch_blocking_wrapper_dependent_command_count,
        accounting
            .reviewer_proof_command_deck
            .launch_blocking_wrapper_dependent_command_count
    );
    assert!(accounting
        .certification_wrapper_free_gate
        .wrapper_dependency_blocker_ids
        .is_empty());
    assert_eq!(
        accounting
            .certification_wrapper_free_gate
            .rust_reviewer_command,
        "clean replacement status --json"
    );
    assert_eq!(
        accounting
            .certification_wrapper_free_gate
            .rust_reviewer_json_pointer,
        "/readiness_accounting/certification_wrapper_free_gate"
    );
    assert!(
        accounting
            .certification_wrapper_free_gate
            .rust_reviewer_command_wrapper_free
    );
    assert_eq!(
        accounting
            .certification_wrapper_free_gate
            .required_reviewer_assertions_schema_version,
        CERTIFICATION_WRAPPER_FREE_ASSERTIONS_SCHEMA_VERSION
    );
    assert_eq!(
        accounting
            .certification_wrapper_free_gate
            .required_reviewer_assertion_count,
        CERTIFICATION_WRAPPER_FREE_ASSERTION_COUNT
    );
    assert_eq!(
        accounting
            .certification_wrapper_free_gate
            .required_reviewer_assertions
            .len(),
        accounting
            .certification_wrapper_free_gate
            .required_reviewer_assertion_count
    );
    assert!(accounting
        .certification_wrapper_free_gate
        .required_reviewer_assertions
        .iter()
        .all(|assertion| assertion
            .json_pointer
            .starts_with("/readiness_accounting/certification_wrapper_free_gate/")
            && !assertion.expected_json.contains("python")));
    assert!(accounting
        .certification_wrapper_free_gate
        .required_reviewer_assertions
        .iter()
        .any(|assertion| assertion
            .json_pointer
            .ends_with("/wrapper_dependency_blocker_ids")
            && assertion.expected_json == "[]"));
    assert!(
        accounting
            .certification_wrapper_free_gate
            .required_reviewer_assertions_json_pointers_unique
    );
    assert_eq!(
        accounting
            .certification_wrapper_free_gate
            .required_reviewer_assertions
            .iter()
            .map(|assertion| assertion.json_pointer)
            .collect::<BTreeSet<_>>()
            .len(),
        accounting
            .certification_wrapper_free_gate
            .required_reviewer_assertion_count
    );
    assert!(
        accounting
            .certification_wrapper_free_gate
            .required_reviewer_assertions_json_pointers_parseable
    );
    assert!(accounting
        .certification_wrapper_free_gate
        .required_reviewer_assertions
        .iter()
        .all(|assertion| json_pointer_is_absolute_and_parseable(assertion.json_pointer)));
    assert!(
        accounting
            .certification_wrapper_free_gate
            .required_reviewer_assertions_json_pointers_dereferenceable
    );
    assert!(accounting
        .certification_wrapper_free_gate
        .required_reviewer_assertions
        .iter()
        .all(
            |assertion| certification_wrapper_free_assertion_actual_json(
                assertion.json_pointer,
                accounting.certification_python_dependency_count,
                accounting
                    .certification_wrapper_free_gate
                    .wrapper_dependent_proof_surface_count,
                accounting
                    .certification_wrapper_free_gate
                    .wrapper_dependent_command_count,
                accounting
                    .certification_wrapper_free_gate
                    .launch_blocking_wrapper_dependent_command_count,
                &accounting
                    .certification_wrapper_free_gate
                    .wrapper_dependency_blocker_ids,
                accounting
                    .certification_wrapper_free_gate
                    .rust_reviewer_command_wrapper_free,
            )
            .is_some()
        ));

    assert_launch_blocker_accounting_tail(&report);
}
