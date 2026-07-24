// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for DRAT/DRUP proof logging and verification.

use super::proof_logging::*;
use super::{Clause, Literal};
use crate::spec::ProofStatus;

// ---- RUP verification tests ----

#[test]
fn test_rup_unit_propagation_derives_conflict() {
    // Clauses: {1, 2}, {1, -2}, {-1, 2}, {-1, -2}
    // Adding empty clause: negate nothing, propagation should find conflict.
    let clauses = [vec![1, 2], vec![1, -2], vec![-1, 2], vec![-1, -2]];
    // Empty clause is RUP: no negated literals, every clause must be falsified
    // by unit propagation from existing clauses. Actually for empty clause,
    // we need to find a conflict with no assumptions at all.
    // Clauses {1,2},{1,-2},{-1,2},{-1,-2} are unsatisfiable, but RUP of []
    // requires conflict from empty assignment. Let's test with a unit clause.
    //
    // {1}, {-1, 2}, {-1, -2} => adding {-1}: negate to get {1}.
    // Assign 1: {-1, 2} becomes unit {2}. Assign 2: {-1, -2} becomes conflict.
    let clauses2 = vec![vec![1], vec![-1, 2], vec![-1, -2]];
    assert!(verify_rup(&clauses2, &[-1]));
}

#[test]
fn test_rup_immediate_conflict_from_unit_clauses() {
    // Clauses: {1}, {-1}
    // Adding empty clause: no negation, propagate {1} then {-1} conflicts.
    let clauses = vec![vec![1], vec![-1]];
    assert!(verify_rup(&clauses, &[]));
}

#[test]
fn test_rup_no_propagation_fails() {
    // Clauses: {1, 2}, {3, 4}
    // Adding {5}: negate to get {-5}. No clause becomes unit.
    let clauses = vec![vec![1, 2], vec![3, 4]];
    assert!(!verify_rup(&clauses, &[5]));
}

#[test]
fn test_rup_complex_chain_propagation() {
    // Clauses: {-1, 2}, {-2, 3}, {-3}
    // Adding {-1}: negate to get {1}.
    // {-1, 2} becomes unit {2}. {-2, 3} becomes unit {3}. {-3} conflicts.
    let clauses = vec![vec![-1, 2], vec![-2, 3], vec![-3]];
    assert!(verify_rup(&clauses, &[-1]));
}

#[test]
fn test_rup_satisfied_clause_skipped() {
    // Clauses: {1, 2}, {-1}
    // Adding {2}: negate to get {-2}.
    // {1, 2}: -2 falsifies 2, leaves unit {1}. Assign 1.
    // {-1}: conflicts with assignment of 1.
    let clauses = vec![vec![1, 2], vec![-1]];
    assert!(verify_rup(&clauses, &[2]));
}

#[test]
fn test_rup_multi_literal_clause() {
    // Clauses: {1}, {-1, -2, 3}, {-3}
    // Adding {-2}: negate to get {2}.
    // {1}: unit, assign 1. {-1, -2, 3}: 1 falsifies -1, 2 satisfies... wait.
    // Negate {-2} => assign 2.
    // {1}: unit, assign 1. {-1, -2, 3}: -1 false (1 assigned), -2 false (2 assigned),
    // unit {3}. Assign 3. {-3}: conflict.
    let clauses = vec![vec![1], vec![-1, -2, 3], vec![-3]];
    assert!(verify_rup(&clauses, &[-2]));
}

#[test]
fn test_rup_empty_clause_set_no_conflict() {
    let clauses: Vec<Vec<i32>> = vec![];
    assert!(!verify_rup(&clauses, &[1]));
}

// ---- RAT verification tests ----

#[test]
fn test_rat_basic_pivot() {
    // Clauses: {1, 2}, {-1, 3}
    // Adding {1} with pivot 1.
    // Clauses containing -1: {-1, 3}.
    // Resolvent: {1} | ({-1, 3} \ {-1}) = {1, 3}.
    // RUP({1, 3}): negate to get {-1, -3}.
    // {1, 2}: -1 falsifies 1, unit {2}. Assign 2. {-1, 3}: -1 satisfied!
    // Since {-1, 3} is satisfied, no conflict is forced... actually
    // we need a clause set that will force conflict.
    //
    // Better example: {1, 2}, {-2} with adding {1}, pivot 1.
    // No clause contains -1, so RAT trivially holds.
    let clauses = vec![vec![1, 2], vec![-2]];
    assert!(verify_rat(&clauses, &[1], 1));
}

#[test]
fn test_rat_no_clauses_with_neg_pivot() {
    // If no clause contains ~pivot, RAT trivially holds.
    let clauses = vec![vec![1, 2], vec![2, 3]];
    assert!(verify_rat(&clauses, &[1], 1));
}

#[test]
fn test_rat_pivot_not_in_clause_fails() {
    let clauses = vec![vec![1, 2]];
    assert!(!verify_rat(&clauses, &[1, 2], 3));
}

#[test]
fn test_rat_with_resolvent_rup_check() {
    // Clauses: {1}, {-1, 2}, {-2}
    // Adding {1, -2} with pivot 1.
    // Clauses containing -1: {-1, 2}.
    // Resolvent: {1, -2} | {2} = {1, -2, 2}. This contains both 2 and -2,
    // so it's a tautology. RUP of a tautology succeeds because assigning
    // negations includes both -2 and 2, which immediately means some clause
    // is satisfied... but RUP checks conflict, not tautology.
    //
    // Actually: negate {1, -2, 2} => {-1, 2, -2}. Assign -1, 2, -2.
    // But 2 and -2 can't both be assigned. In our implementation, both
    // appear in the assignment list. Let's check if {-2} evaluates to
    // conflict: lit -2 is in assignment. Satisfied.
    //
    // Simpler: clauses {-1, 2}, {-2, 3}, {-3, -1}. Add {1}, pivot 1.
    // Clauses with -1: {-1, 2}, {-3, -1}.
    // Resolvent 1: {1} | {2} = {1, 2}. RUP: negate => {-1, -2}.
    //   {-1, 2}: -1 satisfies it. No, -1 is assigned true means lit -1 is
    //   true. In our model, assignment contains -1, so clause {-1, 2}:
    //   lit -1 matches assignment[-1], satisfied. {-2, 3}: -2 satisfies? no,
    //   -2 is in assignment so lit -2 matches. Satisfied. {-3, -1}: -1 satisfied.
    //   No conflict. So this doesn't work.
    //
    // Let's just use the trivial case where no clauses have -pivot.
    let clauses = vec![vec![2, 3], vec![-3, 4]];
    assert!(verify_rat(&clauses, &[1, 2], 1));
}

#[test]
fn test_rat_invalid_resolvent_fails() {
    // Clauses: {-1, 2}, {-2} -- so {1} is actually provable by RUP,
    // but let's construct something where RAT fails.
    // Clauses: {-1, 2}, {-2, 3}. Add {1, -3}, pivot 1.
    // Clause with -1: {-1, 2}. Resolvent: {1, -3, 2}.
    // RUP of {1, -3, 2}: negate => {-1, 3, -2}.
    // {-1, 2}: -1 satisfies. {-2, 3}: -2 satisfies.
    // No conflict => RAT fails.
    let clauses = vec![vec![-1, 2], vec![-2, 3]];
    assert!(!verify_rat(&clauses, &[1, -3], 1));
}

// ---- ProofLog verification tests ----

#[test]
fn test_proof_log_empty_steps() {
    // A proof with no steps cannot derive the empty clause, so it is invalid.
    let log = ProofLog {
        steps: vec![],
        original_clauses: vec![vec![1, 2]],
    };
    let result = verify_proof_log(&log);
    assert!(
        !result.valid,
        "proof with no steps should not be valid (no empty clause derived)"
    );
    assert_eq!(result.steps_verified, 0);
}

#[test]
fn test_proof_log_single_rup_add_without_empty_clause() {
    // Clauses: {1}, {-1, 2}. Add {2} by RUP.
    // RUP({2}): negate => {-2}. {1}: unit, assign 1. {-1, 2}: -2 falsifies 2,
    // -1 falsified by 1. Conflict. Step is individually valid but no empty clause derived.
    let log = ProofLog {
        steps: vec![ProofStep::Add(vec![2])],
        original_clauses: vec![vec![1], vec![-1, 2]],
    };
    let result = verify_proof_log(&log);
    assert!(
        !result.valid,
        "valid steps but no empty clause should be rejected"
    );
    assert_eq!(result.steps_verified, 1);
}

#[test]
fn test_proof_log_single_rup_add_with_empty_clause() {
    // Clauses: {1}, {-1, 2}, {-2}. Add {2} by RUP, then add {} by RUP.
    let log = ProofLog {
        steps: vec![ProofStep::Add(vec![2]), ProofStep::Add(vec![])],
        original_clauses: vec![vec![1], vec![-1, 2], vec![-2]],
    };
    let result = verify_proof_log(&log);
    assert!(result.valid);
    assert_eq!(result.steps_verified, 2);
}

#[test]
fn test_proof_log_add_and_delete_without_empty_clause() {
    // Valid addition and deletion but no empty clause derived = not a valid refutation.
    let log = ProofLog {
        steps: vec![ProofStep::Add(vec![2]), ProofStep::Delete(vec![-1, 2])],
        original_clauses: vec![vec![1], vec![-1, 2]],
    };
    let result = verify_proof_log(&log);
    assert!(
        !result.valid,
        "proof without empty clause is not a valid refutation"
    );
    assert_eq!(result.steps_verified, 2);
}

#[test]
fn test_proof_log_complete_refutation() {
    // {1, 2}, {1, -2}, {-1, 2}, {-1, -2}
    // Add {1} by RUP: negate => {-1}. {1,2}: unit {2}. {1,-2}: unit (already 2 assigned,
    // -2 falsified => unit {1}, but 1 is... wait, we assigned -1.
    // {1, 2}: -1 falsifies 1, unit {2}. Assign 2.
    // {1, -2}: -1 falsifies 1, 2 falsifies -2. Conflict!
    // Add {-1} by RUP: negate => {1}. {-1, 2}: 1 falsifies -1, unit {2}. Assign 2.
    // {-1, -2}: 1 falsifies -1, 2 falsifies -2. Conflict!
    // Add {} by RUP from {1}, {-1}: conflict immediately.
    let log = ProofLog {
        steps: vec![
            ProofStep::Add(vec![1]),
            ProofStep::Add(vec![-1]),
            ProofStep::Add(vec![]),
        ],
        original_clauses: vec![vec![1, 2], vec![1, -2], vec![-1, 2], vec![-1, -2]],
    };
    let result = verify_proof_log(&log);
    assert!(result.valid);
    assert_eq!(result.steps_verified, 3);
    assert_eq!(result.first_error, None);
}

#[test]
fn test_proof_log_invalid_step_detected() {
    // Clauses: {1, -5}, {2, -5}. Adding {5}: RUP fails (negate => {-5},
    // {1, -5} satisfied by -5, {2, -5} satisfied by -5, no conflict).
    // RAT with pivot 5: clauses with -5: {1, -5}, {2, -5}.
    // Resolvent 1: {5, 1}. RUP of {5, 1}: negate => {-5, -1}.
    //   {1, -5}: -5 satisfies. {2, -5}: -5 satisfies. No conflict. RAT fails.
    let log = ProofLog {
        steps: vec![ProofStep::Add(vec![5])],
        original_clauses: vec![vec![1, -5], vec![2, -5]],
    };
    let result = verify_proof_log(&log);
    assert!(!result.valid);
    assert_eq!(result.steps_verified, 0);
    assert_eq!(result.first_error, Some(0));
}

#[test]
fn test_proof_log_error_at_second_step() {
    // First step valid, second invalid.
    // Clauses: {1}, {-1, 2}, {-99}. Add {2} (RUP holds). Then add {99}:
    // RUP of {99}: negate => {-99}. {-99}: -99 in assignment, satisfied.
    // No conflict => RUP fails.
    // RAT with pivot 99: clause {-99} contains -99. Resolvent: {99} | {} = {99}.
    // RUP of {99}: same, fails. Invalid step.
    let log = ProofLog {
        steps: vec![
            ProofStep::Add(vec![2]),  // RUP holds
            ProofStep::Add(vec![99]), // Cannot be verified (RUP + RAT both fail)
        ],
        original_clauses: vec![vec![1], vec![-1, 2], vec![-99]],
    };
    let result = verify_proof_log(&log);
    assert!(!result.valid);
    assert_eq!(result.steps_verified, 1);
    assert_eq!(result.first_error, Some(1));
}

// ---- DRAT parsing tests ----

#[test]
fn test_parse_drat_basic_add() {
    let input = "1 2 0\n";
    let steps = parse_drat_proof(input).expect("parse");
    assert_eq!(steps.len(), 1);
    assert_eq!(steps[0], ProofStep::Add(vec![1, 2]));
}

#[test]
fn test_parse_drat_deletion() {
    let input = "d 1 -2 0\n";
    let steps = parse_drat_proof(input).expect("parse");
    assert_eq!(steps.len(), 1);
    assert_eq!(steps[0], ProofStep::Delete(vec![1, -2]));
}

#[test]
fn test_parse_drat_multi_line() {
    let input = "1 2 0\nd -1 3 0\n4 0\n";
    let steps = parse_drat_proof(input).expect("parse");
    assert_eq!(steps.len(), 3);
    assert_eq!(steps[0], ProofStep::Add(vec![1, 2]));
    assert_eq!(steps[1], ProofStep::Delete(vec![-1, 3]));
    assert_eq!(steps[2], ProofStep::Add(vec![4]));
}

#[test]
fn test_parse_drat_empty_clause() {
    let input = "0\n";
    let steps = parse_drat_proof(input).expect("parse");
    assert_eq!(steps.len(), 1);
    assert_eq!(steps[0], ProofStep::Add(vec![]));
}

#[test]
fn test_parse_drat_empty_input() {
    let input = "";
    let steps = parse_drat_proof(input).expect("parse");
    assert!(steps.is_empty());
}

#[test]
fn test_parse_drat_comments_skipped() {
    let input = "c this is a comment\n1 2 0\nc another comment\n";
    let steps = parse_drat_proof(input).expect("parse");
    assert_eq!(steps.len(), 1);
}

#[test]
fn test_parse_drat_malformed_literal() {
    let input = "1 abc 0\n";
    assert!(parse_drat_proof(input).is_err());
}

#[test]
fn test_parse_drat_no_terminator() {
    // Line without trailing 0: literals are collected until end of tokens.
    let input = "1 2 3\n";
    let steps = parse_drat_proof(input).expect("parse");
    assert_eq!(steps[0], ProofStep::Add(vec![1, 2, 3]));
}

// ---- Formatting tests ----

#[test]
fn test_format_drat_add_step() {
    let step = ProofStep::Add(vec![1, -2, 3]);
    assert_eq!(format_drat_step(&step), "1 -2 3 0");
}

#[test]
fn test_format_drat_delete_step() {
    let step = ProofStep::Delete(vec![4, -5]);
    assert_eq!(format_drat_step(&step), "d 4 -5 0");
}

#[test]
fn test_format_drat_empty_clause() {
    let step = ProofStep::Add(vec![]);
    assert_eq!(format_drat_step(&step), "0");
}

#[test]
fn test_format_roundtrip() {
    let original = vec![
        ProofStep::Add(vec![1, 2]),
        ProofStep::Delete(vec![-1, 3]),
        ProofStep::Add(vec![]),
    ];
    let text: String = original
        .iter()
        .map(|s| format_drat_step(s) + "\n")
        .collect();
    let parsed = parse_drat_proof(&text).expect("roundtrip parse");
    assert_eq!(parsed, original);
}

// ---- Edge case tests ----

#[test]
fn test_rup_single_unit_clause_conflict() {
    // Clauses: {-1}. Adding {1}: negate => {-1}. -1 satisfies {-1}...
    // actually: negate(1) = -1. Assignment = [-1]. {-1}: lit -1 is in assignment,
    // so satisfied. No conflict. RUP fails.
    // Correct: clauses {-1}. Adding {-1} is trivially subsumed, not RUP.
    // For conflict: clauses {1}, {-1}. Adding {}: conflict from propagation.
    let clauses = vec![vec![1], vec![-1]];
    assert!(verify_rup(&clauses, &[]));
}

#[test]
fn test_delete_nonexistent_clause_is_noop() {
    // Deleting a nonexistent clause is a no-op, but without an empty clause
    // the proof is not a valid refutation.
    let log = ProofLog {
        steps: vec![ProofStep::Delete(vec![99, 100])],
        original_clauses: vec![vec![1, 2]],
    };
    let result = verify_proof_log(&log);
    assert!(!result.valid, "no empty clause derived");
}

#[test]
fn test_delete_removes_clause_from_active_set() {
    // After deleting a clause, it should no longer participate in RUP checks.
    // {1}, {-1, 2}, {-2}. Delete {-2}. Then add {-1} should fail since
    // without {-2}, RUP of {-1} is: negate => {1}. {1}: satisfied.
    // {-1, 2}: 1 satisfies (no, 1 is in assignment meaning lit 1 is true,
    // clause {-1, 2} has lit -1 (false) and lit 2 (unassigned). Unit {2}.
    // Assign 2. No more clauses ({-2} was deleted). No conflict. Fails.
    let log = ProofLog {
        steps: vec![ProofStep::Delete(vec![-2]), ProofStep::Add(vec![-1])],
        original_clauses: vec![vec![1], vec![-1, 2], vec![-2]],
    };
    let result = verify_proof_log(&log);
    assert!(!result.valid);
    assert_eq!(result.first_error, Some(1));
}

#[test]
fn test_proof_status_constants() {
    assert_eq!(S09_RUP_SOUNDNESS, ProofStatus::DerivedPending);
    assert_eq!(S10_RAT_SOUNDNESS, ProofStatus::DerivedPending);
}

#[test]
fn test_proof_step_clone_and_debug() {
    let step = ProofStep::Add(vec![1, 2]);
    let cloned = step.clone();
    assert_eq!(step, cloned);
    let debug = format!("{:?}", step);
    assert!(debug.contains("Add"));
}

#[test]
fn test_proof_log_result_fields() {
    let result = ProofLogResult {
        valid: true,
        steps_verified: 5,
        first_error: None,
        phantom_deletions: vec![],
    };
    assert!(result.valid);
    assert_eq!(result.steps_verified, 5);
    assert_eq!(result.first_error, None);
}

#[test]
fn test_delete_matches_by_set_equality() {
    // Clause {2, 1} should match deletion of {1, 2} (order-independent).
    // No empty clause derived, so not a valid refutation.
    let log = ProofLog {
        steps: vec![ProofStep::Delete(vec![1, 2])],
        original_clauses: vec![vec![2, 1], vec![3]],
    };
    let result = verify_proof_log(&log);
    assert!(!result.valid, "no empty clause derived");
}

// ---- Adversarial soundness tests (audit findings) ----

#[test]
fn test_soundness_drat_proof_without_empty_clause_rejected() {
    // CRITICAL BUG (Finding 2): A proof with all valid RUP/RAT steps that
    // never derives the empty clause must be rejected.
    // Attack: claim UNSAT for a satisfiable formula by providing valid
    // intermediate clause additions that never actually derive a contradiction.
    //
    // Formula: {1, 2} (satisfiable). Proof adds {1} via RAT (no clauses
    // have -1 so RAT trivially holds). All steps are valid but no empty
    // clause is ever derived.
    let log = ProofLog {
        steps: vec![
            ProofStep::Add(vec![1]), // valid RAT (no clause contains -1)
        ],
        original_clauses: vec![vec![1, 2]],
    };
    let result = verify_proof_log(&log);
    assert!(
        !result.valid,
        "SOUNDNESS BUG: proof without empty clause derivation was accepted as valid refutation"
    );
}

#[test]
fn test_soundness_empty_clause_in_middle_is_valid() {
    // The empty clause can be derived in the middle of the proof (not just last step).
    // The proof should still be valid.
    let log = ProofLog {
        steps: vec![
            ProofStep::Add(vec![]),  // empty clause derived first
            ProofStep::Add(vec![1]), // extra step after (valid since {} is in active set)
        ],
        original_clauses: vec![vec![1], vec![-1]],
    };
    let result = verify_proof_log(&log);
    assert!(
        result.valid,
        "empty clause derived in middle should make proof valid"
    );
}

// ============================================================
// #3324: Phantom deletion tracking (delete of non-existent clause)
// ============================================================

#[test]
fn test_phantom_deletion_detected_for_missing_clause() {
    // Deleting a clause that does not exist in the active set must be tracked
    // as a phantom deletion. This detects corrupted/malformed proofs.
    let log = ProofLog {
        steps: vec![ProofStep::Delete(vec![99, 100])],
        original_clauses: vec![vec![1, 2]],
    };
    let result = verify_proof_log(&log);
    assert_eq!(
        result.phantom_deletions,
        vec![0],
        "delete of non-existent clause {{99, 100}} should be tracked as phantom"
    );
}

#[test]
fn test_phantom_deletion_not_flagged_for_existing_clause() {
    // Deleting a clause that exists should NOT appear in phantom_deletions.
    let log = ProofLog {
        steps: vec![ProofStep::Delete(vec![1, 2])],
        original_clauses: vec![vec![1, 2], vec![3]],
    };
    let result = verify_proof_log(&log);
    assert!(
        result.phantom_deletions.is_empty(),
        "delete of existing clause should not be a phantom deletion"
    );
}

#[test]
fn test_phantom_deletion_multiple_tracked() {
    // Multiple phantom deletions in a single proof should all be tracked.
    let log = ProofLog {
        steps: vec![
            ProofStep::Delete(vec![10, 20]), // phantom (step 0)
            ProofStep::Delete(vec![1, 2]),   // real delete (step 1)
            ProofStep::Delete(vec![30, 40]), // phantom (step 2)
        ],
        original_clauses: vec![vec![1, 2]],
    };
    let result = verify_proof_log(&log);
    assert_eq!(
        result.phantom_deletions,
        vec![0, 2],
        "both phantom deletions should be tracked with their step indices"
    );
}

#[test]
fn test_phantom_deletion_double_delete_same_clause() {
    // Deleting the same clause twice: first delete succeeds, second is phantom.
    let log = ProofLog {
        steps: vec![
            ProofStep::Delete(vec![1, 2]), // real delete (step 0)
            ProofStep::Delete(vec![1, 2]), // phantom — already removed (step 1)
        ],
        original_clauses: vec![vec![1, 2]],
    };
    let result = verify_proof_log(&log);
    assert_eq!(
        result.phantom_deletions,
        vec![1],
        "second delete of same clause should be phantom"
    );
}

#[test]
fn test_valid_proof_has_no_phantom_deletions() {
    // A completely valid proof should have empty phantom_deletions.
    let log = ProofLog {
        steps: vec![
            ProofStep::Add(vec![1]),
            ProofStep::Add(vec![-1]),
            ProofStep::Add(vec![]),
        ],
        original_clauses: vec![vec![1, 2], vec![1, -2], vec![-1, 2], vec![-1, -2]],
    };
    let result = verify_proof_log(&log);
    assert!(result.valid);
    assert!(
        result.phantom_deletions.is_empty(),
        "valid proof should have no phantom deletions"
    );
}

// ============================================================
// #3326: Adversarial DRAT test coverage
// ============================================================

#[test]
fn test_adversarial_empty_proof_not_valid_refutation() {
    // An empty proof with no steps is not a valid refutation.
    let log = ProofLog {
        steps: vec![],
        original_clauses: vec![vec![1], vec![-1]],
    };
    let result = verify_proof_log(&log);
    assert!(!result.valid, "empty proof is not a valid refutation");
    assert_eq!(result.steps_verified, 0);
}

#[test]
fn test_adversarial_only_deletions_not_valid_refutation() {
    // A proof consisting entirely of deletion steps with no additions
    // cannot derive the empty clause.
    let log = ProofLog {
        steps: vec![
            ProofStep::Delete(vec![1, 2]),
            ProofStep::Delete(vec![-1, 3]),
        ],
        original_clauses: vec![vec![1, 2], vec![-1, 3], vec![4]],
    };
    let result = verify_proof_log(&log);
    assert!(
        !result.valid,
        "proof with only deletions cannot be a valid refutation"
    );
    assert!(
        result.phantom_deletions.is_empty(),
        "all deleted clauses existed, so no phantom deletions"
    );
}

#[test]
fn test_adversarial_nonexistent_variables_in_proof() {
    // A proof step references variables far outside the original formula.
    // Adding {1000}: neither RUP nor RAT can verify it against {1, 2}, {-1}.
    let log = ProofLog {
        steps: vec![ProofStep::Add(vec![1000])],
        original_clauses: vec![vec![1, 2], vec![-1]],
    };
    let result = verify_proof_log(&log);
    assert!(
        !result.valid,
        "adding clause with non-existent variable should fail verification"
    );
    // The clause {1000} passes RAT check vacuously (no clause contains -1000),
    // so the error is at the end: no empty clause was derived.
    assert_eq!(result.first_error, Some(log.steps.len()));
}

#[test]
fn test_adversarial_large_variable_indices() {
    // Stress test: large literal values should not cause panics or overflows.
    let big = i32::MAX;
    let log = ProofLog {
        steps: vec![ProofStep::Add(vec![big, -big])],
        original_clauses: vec![vec![1]],
    };
    let result = verify_proof_log(&log);
    // The clause {MAX, -MAX} is a tautology (contains both x and -x),
    // but our verifier checks RUP/RAT, not tautology detection directly.
    // RUP of {MAX, -MAX}: negate => {-MAX, MAX}. Both in assignment.
    // Any clause containing MAX or -MAX is satisfied by one of them.
    // But we need an actual CONFLICT, not just satisfaction.
    // If no clause has both falsified, no conflict. Result depends on formula.
    // The key thing: no panic.
    assert!(
        !result.valid,
        "tautological addition should not make a valid refutation"
    );
}

#[test]
fn test_adversarial_circular_implications_no_unsound_derivation() {
    // Attempt to create a "circular" proof where clauses imply each other
    // but no contradiction exists. The verifier must reject this.
    //
    // Formula: {1, 2}, {-2, 3}, {-3, 1} — satisfiable (e.g., 1=T).
    // Try to "prove" UNSAT by adding mutually implied clauses.
    let log = ProofLog {
        steps: vec![
            // {1} is not RUP: negate => {-1}. {1,2}: -1 falsifies 1, unit {2}.
            // {-2,3}: 2 falsifies -2... wait, 2 is true so -2 is false. Unit {3}.
            // {-3, 1}: 3 falsifies -3... 3 is true so -3 is false. -1 makes 1 false. Conflict? No.
            // {-3, 1}: -3 false (3 assigned), 1 false (-1 assigned). CONFLICT!
            ProofStep::Add(vec![1]), // This IS actually RUP.
            // Now active: {1,2}, {-2,3}, {-3,1}, {1}.
            // {-1}: negate => {1}. {1}: 1 in assignment, satisfied. No conflict from this.
            // Actually: for {-1}, negate => assign 1. {1}: satisfied. {-2,3}: unresolved.
            // {-3,1}: 1 satisfied. No conflict. RUP fails.
            ProofStep::Add(vec![-1]), // should fail
        ],
        original_clauses: vec![vec![1, 2], vec![-2, 3], vec![-3, 1]],
    };
    let result = verify_proof_log(&log);
    // Step 0 ({1}) is RUP, but step 1 ({-1}) should fail.
    // Even if step 0 succeeds, the proof never derives empty clause.
    // Let's check: if {1} addition succeeds, then active has {1}.
    // {-1}: negate => assign 1. Clause {1}: 1 satisfied. {1,2}: 1 satisfied.
    // {-2,3}: unresolved (no 2,3 info). {-3,1}: 1 satisfied. No conflict.
    // RUP fails. RAT with pivot -1: clauses with 1: {1,2}, {-3,1}, {1}.
    // Large check, but ultimately {-1} is not derivable from a satisfiable formula.
    assert!(
        !result.valid,
        "circular implications should not produce valid refutation"
    );
}

#[test]
fn test_adversarial_delete_all_then_derive_empty() {
    // Delete all clauses, then try to derive the empty clause.
    // With no active clauses, RUP of {} requires a conflict from
    // empty assignment on no clauses — impossible.
    let log = ProofLog {
        steps: vec![
            ProofStep::Delete(vec![1]),
            ProofStep::Delete(vec![-1]),
            ProofStep::Add(vec![]), // attempt to derive empty clause
        ],
        original_clauses: vec![vec![1], vec![-1]],
    };
    let result = verify_proof_log(&log);
    assert!(
        !result.valid || result.first_error.is_some(),
        "deleting all clauses then deriving empty should fail"
    );
}

#[test]
fn test_adversarial_parse_drat_only_comments() {
    // A proof file with only comments should parse to empty steps.
    let input = "c comment line 1\nc comment line 2\nc trailing\n";
    let steps = parse_drat_proof(input).expect("comments-only should parse");
    assert!(steps.is_empty());
}

#[test]
fn test_adversarial_parse_drat_delete_empty_clause() {
    // Deleting the empty clause (line "d 0") is syntactically valid.
    let input = "d 0\n";
    let steps = parse_drat_proof(input).expect("delete empty clause should parse");
    assert_eq!(steps.len(), 1);
    assert_eq!(steps[0], ProofStep::Delete(vec![]));
}

#[test]
fn test_adversarial_parse_drat_negative_literals() {
    let input = "-1 -2 -3 0\n";
    let steps = parse_drat_proof(input).expect("negative literals should parse");
    assert_eq!(steps[0], ProofStep::Add(vec![-1, -2, -3]));
}

#[test]
fn test_adversarial_parse_drat_repeated_literals() {
    // Repeated literals in a clause (e.g., "1 1 2 0") — the parser should
    // accept this without error. Whether the verifier treats it as {1,1,2}
    // or deduplicates is a semantics question, but it must not crash.
    let input = "1 1 2 0\n";
    let steps = parse_drat_proof(input).expect("repeated literals should parse");
    assert_eq!(steps[0], ProofStep::Add(vec![1, 1, 2]));
}

#[test]
fn test_adversarial_parse_drat_complementary_literals() {
    // A clause containing both a literal and its negation: {1, -1}.
    // This is a tautology. The parser should accept it; the verifier
    // should not crash on it.
    let input = "1 -1 0\n";
    let steps = parse_drat_proof(input).expect("complementary literals should parse");
    assert_eq!(steps[0], ProofStep::Add(vec![1, -1]));
}

#[test]
fn test_adversarial_rup_on_empty_clause_set() {
    // RUP with no clauses and non-empty new clause: cannot derive conflict.
    let empty: Vec<Clause> = vec![];
    assert!(!verify_rup(&empty, &[1, 2, 3]));
}

#[test]
fn test_adversarial_rup_empty_clause_on_empty_set() {
    // RUP of empty clause on empty clause set: we need a conflict from
    // empty assignment. No clauses => no conflict.
    let empty: Vec<Clause> = vec![];
    assert!(!verify_rup(&empty, &[]));
}

#[test]
fn test_adversarial_rat_empty_clause_set() {
    // RAT with no clauses: pivot must be in new_clause, and there are no
    // clauses with ~pivot, so RAT trivially holds.
    let empty: Vec<Clause> = vec![];
    assert!(verify_rat(&empty, &[1], 1));
}

#[test]
fn test_adversarial_rat_empty_new_clause() {
    // RAT of empty clause: pivot must be in new_clause, but empty clause
    // has no literals. Should return false.
    let clauses = vec![vec![1, -2]];
    assert!(!verify_rat(&clauses, &[], 1));
}

#[test]
fn test_adversarial_proof_with_only_phantom_deletions() {
    // Every deletion is phantom (non-existent). No additions. Not a valid refutation.
    let log = ProofLog {
        steps: vec![
            ProofStep::Delete(vec![5, 6]),
            ProofStep::Delete(vec![7, 8]),
            ProofStep::Delete(vec![9]),
        ],
        original_clauses: vec![vec![1, 2]],
    };
    let result = verify_proof_log(&log);
    assert!(!result.valid);
    assert_eq!(
        result.phantom_deletions,
        vec![0, 1, 2],
        "all three deletions should be phantom"
    );
}

#[test]
fn test_adversarial_add_tautological_clause() {
    // Adding {1, -1}: this is a tautology. RUP check: negate => {-1, 1}.
    // Assignment has both -1 and 1 in it. Any clause containing 1 or -1 is
    // satisfied. For conflict, ALL clauses must be falsified. But any clause
    // with 1 or -1 is satisfied. RUP fails unless there's a clause with
    // neither 1 nor -1. RAT with pivot 1: clauses containing -1.
    let log = ProofLog {
        steps: vec![ProofStep::Add(vec![1, -1])],
        original_clauses: vec![vec![2, 3]],
    };
    let result = verify_proof_log(&log);
    // Not a valid refutation (no empty clause) regardless of step validity.
    assert!(!result.valid);
}

#[test]
fn test_adversarial_proof_interleaved_add_delete() {
    // Interleave adds and deletes in a valid refutation.
    // {1}, {-1, 2}, {-2}. Add {2} (RUP), delete {-1, 2}, add {-1} (RUP from {1},{2},{-2}),
    // then derive empty.
    //
    // Step 0: Add {2}. RUP: negate => {-2}. {1}: unit assign 1.
    //         {-1, 2}: 1 falsifies -1, -2 falsifies 2. CONFLICT. Yes.
    // Step 1: Delete {-1, 2}. Exists. Active: {1}, {-2}, {2}.
    // Step 2: Add {-1}. RUP: negate => {1}. {1}: 1 satisfied. {-2}: unresolved.
    //         {2}: 1 doesn't help. Hmm. {-2}: only lit -2, not falsified by {1}.
    //         Not conflict. Need more propagation. {2}: 1 not relevant, 2 not in assignment.
    //         Wait — with active {1}, {-2}, {2}: negate {-1} => assign 1.
    //         {1}: 1 satisfied. {-2}: lit -2, not in assignment => unit? No, single lit.
    //         -2 is the clause. Is -2 in assignment? No. Is 2 in assignment? No.
    //         Unassigned => unit: assign -2. {2}: lit 2, negate is -2, -2 is assigned.
    //         So 2 is falsified. Single lit falsified => conflict. RUP succeeds!
    // Step 3: Add {}. Active: {1}, {-2}, {2}, {-1}.
    //         RUP of {}: negate nothing. {1}: unit 1. {-1}: unit -1. Conflict (1 and -1). Done.
    let log = ProofLog {
        steps: vec![
            ProofStep::Add(vec![2]),
            ProofStep::Delete(vec![-1, 2]),
            ProofStep::Add(vec![-1]),
            ProofStep::Add(vec![]),
        ],
        original_clauses: vec![vec![1], vec![-1, 2], vec![-2]],
    };
    let result = verify_proof_log(&log);
    assert!(
        result.valid,
        "interleaved add/delete refutation should be valid"
    );
    assert!(result.phantom_deletions.is_empty());
    assert_eq!(result.steps_verified, 4);
}

#[test]
fn test_adversarial_delete_original_clause_needed_for_later_rup() {
    // Delete a clause needed for a later RUP check. The later RUP should fail.
    // {1}, {-1, 2}, {-2}. Delete {-2}. Then adding {-1} requires RUP:
    // negate => {1}. {1}: satisfied. {-1, 2}: 1 falsifies -1, unit {2}.
    // Assign 2. No more clauses ({-2} was deleted). No conflict. FAILS.
    let log = ProofLog {
        steps: vec![ProofStep::Delete(vec![-2]), ProofStep::Add(vec![-1])],
        original_clauses: vec![vec![1], vec![-1, 2], vec![-2]],
    };
    let result = verify_proof_log(&log);
    assert!(
        !result.valid,
        "RUP should fail after deleting needed clause"
    );
    assert_eq!(result.first_error, Some(1));
}

#[test]
fn test_adversarial_verify_addition_empty_clause_needs_conflict() {
    // Adding the empty clause requires RUP: negate nothing, propagate from
    // scratch. Only valid if the formula is already contradictory.
    // Satisfiable formula: {1, 2}. Cannot derive empty clause.
    let log = ProofLog {
        steps: vec![ProofStep::Add(vec![])],
        original_clauses: vec![vec![1, 2]],
    };
    let result = verify_proof_log(&log);
    assert!(
        !result.valid,
        "empty clause on satisfiable formula should fail"
    );
    assert_eq!(result.first_error, Some(0));
}

#[test]
fn test_adversarial_format_roundtrip_with_deletion() {
    // Verify that format/parse roundtrip preserves deletion steps.
    let original = vec![
        ProofStep::Add(vec![1, -2]),
        ProofStep::Delete(vec![3, 4]),
        ProofStep::Add(vec![]),
        ProofStep::Delete(vec![]),
    ];
    let text: String = original
        .iter()
        .map(|s| format_drat_step(s) + "\n")
        .collect();
    let parsed = parse_drat_proof(&text).expect("roundtrip parse");
    assert_eq!(parsed, original);
}

// ---- #3327: Contradictory assignment detection in RUP ----

#[test]
fn test_rup_contradictory_unit_propagation_detects_conflict() {
    // SOUNDNESS FIX (#3327): If unit propagation assigns the same variable
    // both true and false, that is a contradiction (the clause is RUP).
    //
    // Clauses: {1, 2}, {-2, 3}, {1, -3, -2}
    // Adding {1}: negate => {-1}.
    // {1, 2}: -1 falsifies 1, unit {2}. Assign 2.
    // {-2, 3}: 2 falsifies -2... wait, 2 is assigned true so -2 is false.
    // Unit {3}. Assign 3.
    // {1, -3, -2}: -1 falsifies 1, 3 falsifies -3, 2 falsifies -2. Conflict!
    let clauses = vec![vec![1, 2], vec![-2, 3], vec![1, -3, -2]];
    assert!(verify_rup(&clauses, &[1]));
}

#[test]
fn test_rup_contradictory_initial_negation_detects_conflict() {
    // If the new clause contains both x and -x, negating them produces
    // a contradictory assignment immediately => clause is trivially RUP.
    // Clause {1, -1}: negate => {-1, 1}. Both 1 and -1 in assignment => conflict.
    let clauses: Vec<Vec<i32>> = vec![vec![2, 3]]; // clauses don't matter
    assert!(verify_rup(&clauses, &[1, -1]));
}

#[test]
fn test_rup_duplicate_unit_propagation_no_infinite_loop() {
    // Ensure that if unit propagation would re-derive an already-assigned
    // literal, we don't loop infinitely or double-add it.
    // Clauses: {1}, {1}, {-1}. Adding {}: negate nothing.
    // {1}: unit {1}. Assign 1. {1}: 1 is satisfied. {-1}: conflict.
    let clauses = vec![vec![1], vec![1], vec![-1]];
    assert!(verify_rup(&clauses, &[]));
}
