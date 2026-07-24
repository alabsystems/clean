// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for learned clause minimization verification.

#[cfg(test)]
mod tests {
    use crate::sat_verify::cdcl::clause_minimization::{
        clause_lbd, clause_subsumes, minimize_learned_clause, self_subsumption, sort_by_activity,
        verify_minimization_sound, vivification_step, MinimizationResult,
        S09_SELF_SUBSUMPTION_SOUND, S10_VIVIFICATION_PRESERVES_ENTAILMENT,
    };
    use crate::spec::ProofStatus;

    // ---- Self-subsumption tests ----

    #[test]
    fn test_self_subsumption_applicable() {
        // clause: {1, 2, 3}, resolvent: {-1, 2}
        // Resolve on var 1: result = {2, 3} union {2} = {2, 3}
        // {2, 3} is a subset of {1, 2, 3}, so self-subsumption applies.
        let clause = vec![1, 2, 3];
        let resolvent = vec![-1, 2];
        let result = self_subsumption(&clause, &resolvent);
        assert!(result.is_some(), "self-subsumption should apply");
        let minimized = result.unwrap();
        assert_eq!(minimized.len(), 2);
        assert!(minimized.contains(&2));
        assert!(minimized.contains(&3));
        assert!(!minimized.contains(&1), "pivot literal should be removed");
    }

    #[test]
    fn test_self_subsumption_not_applicable() {
        // clause: {1, 2}, resolvent: {-1, 3}
        // Resolve on var 1: result = {2, 3}
        // {2, 3} is NOT a subset of {1, 2} (3 not in clause).
        let clause = vec![1, 2];
        let resolvent = vec![-1, 3];
        let result = self_subsumption(&clause, &resolvent);
        assert!(result.is_none(), "self-subsumption should not apply");
    }

    #[test]
    fn test_self_subsumption_empty_clause() {
        let result = self_subsumption(&[], &[1, 2]);
        assert!(result.is_none(), "empty clause cannot be self-subsumed");
    }

    #[test]
    fn test_self_subsumption_empty_resolvent() {
        let result = self_subsumption(&[1, 2], &[]);
        assert!(result.is_none(), "empty resolvent cannot self-subsume");
    }

    #[test]
    fn test_self_subsumption_no_opposite_polarity() {
        // clause: {1, 2}, resolvent: {1, 3} -- same polarity on var 1
        let result = self_subsumption(&[1, 2], &[1, 3]);
        assert!(result.is_none(), "no pivot available");
    }

    #[test]
    fn test_self_subsumption_unit_clause() {
        // clause: {1, 2}, resolvent: {-1}
        // Resolve on var 1: result = {2}
        // {2} is a subset of {1, 2}, so self-subsumption applies.
        let result = self_subsumption(&[1, 2], &[-1]);
        assert!(result.is_some());
        let minimized = result.unwrap();
        assert_eq!(minimized, vec![2]);
    }

    // ---- Clause subsumption tests ----

    #[test]
    fn test_clause_subsumes_true() {
        // {1, 2} subsumes {1, 2, 3}
        assert!(clause_subsumes(&[1, 2], &[1, 2, 3]));
    }

    #[test]
    fn test_clause_subsumes_false() {
        // {1, 4} does NOT subsume {1, 2, 3}
        assert!(!clause_subsumes(&[1, 4], &[1, 2, 3]));
    }

    #[test]
    fn test_clause_subsumes_identical() {
        assert!(clause_subsumes(&[1, 2, 3], &[1, 2, 3]));
    }

    #[test]
    fn test_clause_subsumes_empty_subsumes_all() {
        // Empty clause subsumes everything.
        assert!(clause_subsumes(&[], &[1, 2, 3]));
        assert!(clause_subsumes(&[], &[]));
    }

    #[test]
    fn test_clause_subsumes_nonempty_does_not_subsume_empty() {
        assert!(!clause_subsumes(&[1], &[]));
    }

    #[test]
    fn test_clause_subsumes_polarity_matters() {
        // {1} does NOT subsume {-1, 2}
        assert!(!clause_subsumes(&[1], &[-1, 2]));
    }

    // ---- Minimize learned clause tests ----

    #[test]
    fn test_minimize_learned_clause_reduces() {
        // Learned clause: {1, 2, 3}
        // DB clause: {-1, 2} => self-subsumption yields {2, 3}
        let learned = vec![1, 2, 3];
        let db = vec![vec![-1, 2]];
        let minimized = minimize_learned_clause(&learned, &db);
        assert!(minimized.len() < learned.len(), "should reduce clause size");
        assert!(minimized.contains(&2));
        assert!(minimized.contains(&3));
    }

    #[test]
    fn test_minimize_learned_clause_no_reduction() {
        // No clause in DB enables self-subsumption.
        let learned = vec![1, 2, 3];
        let db = vec![vec![4, 5], vec![6, -7]];
        let minimized = minimize_learned_clause(&learned, &db);
        assert_eq!(minimized, learned);
    }

    #[test]
    fn test_minimize_learned_clause_empty_db() {
        let learned = vec![1, 2, 3];
        let minimized = minimize_learned_clause(&learned, &[]);
        assert_eq!(minimized, learned);
    }

    #[test]
    fn test_minimize_learned_clause_chained_reduction() {
        // Learned: {1, 2, 3, 4}
        // DB[0]: {-1, 2} => reduces to {2, 3, 4}
        // DB[1]: {-3, 2} => reduces to {2, 4}
        let learned = vec![1, 2, 3, 4];
        let db = vec![vec![-1, 2], vec![-3, 2]];
        let minimized = minimize_learned_clause(&learned, &db);
        assert_eq!(minimized.len(), 2);
        assert!(minimized.contains(&2));
        assert!(minimized.contains(&4));
    }

    // ---- Vivification tests ----

    #[test]
    fn test_vivification_step_removes_redundant() {
        // clause: {1, 2, 3}
        // When we negate literal 1 (set -1), propagation implies -2.
        // Since -(-2) = 2 is in the clause, literal 1 is redundant.
        let clause = vec![1, 2, 3];
        let result = vivification_step(&clause, &|units: &[i32]| {
            if units.contains(&-1) {
                Some(-2) // propagating -1 implies -2
            } else {
                None
            }
        });
        assert!(!result.contains(&1), "literal 1 should be removed");
        assert!(result.contains(&2));
        assert!(result.contains(&3));
    }

    #[test]
    fn test_vivification_step_no_removal() {
        // No propagation yields a conflict.
        let clause = vec![1, 2, 3];
        let result = vivification_step(&clause, &|_| None);
        assert_eq!(result, clause);
    }

    #[test]
    fn test_vivification_step_empty_clause() {
        let result = vivification_step(&[], &|_| None);
        assert!(result.is_empty());
    }

    #[test]
    fn test_vivification_step_unit_clause() {
        // Unit clause: cannot remove the only literal (propagating its
        // negation does not imply a conflict with another literal in clause).
        let clause = vec![1];
        let result = vivification_step(&clause, &|_| None);
        assert_eq!(result, vec![1]);
    }

    // ---- Soundness verification (brute force) tests ----

    #[test]
    fn test_verify_sound_subset_clause() {
        // Minimized {1, 2} implies original {1, 2, 3}:
        // every model of {1,2} also satisfies {1,2,3}.
        assert!(verify_minimization_sound(&[1, 2, 3], &[1, 2], 3));
    }

    #[test]
    fn test_verify_sound_identical() {
        assert!(verify_minimization_sound(&[1, 2], &[1, 2], 2));
    }

    #[test]
    fn test_verify_sound_fails_for_incompatible() {
        // Original: {1}, Minimized: {2}
        // Assignment: x1=true, x2=false satisfies {1} but not {2}.
        assert!(!verify_minimization_sound(&[1], &[2], 2));
    }

    #[test]
    fn test_verify_sound_empty_minimized() {
        // Empty minimized clause is never satisfied (represents falsity).
        // Since `min_sat` is always false, `min_sat && !orig_sat` is never
        // true, so the check vacuously passes: the empty clause implies
        // everything.
        assert!(verify_minimization_sound(&[1], &[], 1));
    }

    #[test]
    fn test_verify_sound_empty_original() {
        // Empty original is never satisfied. Minimized {1} can be satisfied.
        // Assignment x1=true: min_sat=true, orig_sat=false => soundness fails.
        assert!(!verify_minimization_sound(&[], &[1], 1));
    }

    #[test]
    fn test_verify_sound_too_many_vars() {
        // Over 20 variables: returns false (too expensive).
        assert!(!verify_minimization_sound(&[1], &[1], 21));
    }

    #[test]
    fn test_verify_sound_subset_is_sound() {
        // Original: {1, -2}, Minimized: {1}
        // {1} implies {1, -2} because every model of {1} (x1=true)
        // trivially satisfies {1, -2}. Sound.
        assert!(verify_minimization_sound(&[1, -2], &[1], 2));
    }

    #[test]
    fn test_verify_sound_not_subset_fails() {
        // Original: {1}, Minimized: {1, -2}
        // {1, -2} does NOT imply {1}: assignment x1=false,x2=false
        // satisfies {1,-2} via -2, but not {1}. Unsound.
        assert!(!verify_minimization_sound(&[1], &[1, -2], 2));
    }

    #[test]
    fn test_verify_sound_self_subsumption_result() {
        // Verify that self-subsumption produces a sound result.
        let clause = vec![1, 2, 3];
        let resolvent = vec![-1, 2];
        let minimized = self_subsumption(&clause, &resolvent).unwrap();
        // The minimized clause should be implied by the original.
        assert!(verify_minimization_sound(&clause, &minimized, 3));
    }

    // ---- LBD tests ----

    #[test]
    fn test_lbd_single_level() {
        // All literals from decision level 1.
        let decision_levels = vec![0, 1, 1, 1]; // index 0 unused
        let clause = vec![1, 2, 3];
        assert_eq!(clause_lbd(&clause, &decision_levels), 1);
    }

    #[test]
    fn test_lbd_multiple_levels() {
        let decision_levels = vec![0, 1, 2, 3, 1];
        let clause = vec![1, 2, 3, 4];
        assert_eq!(clause_lbd(&clause, &decision_levels), 3); // levels 1, 2, 3
    }

    #[test]
    fn test_lbd_empty_clause() {
        let decision_levels = vec![0, 1, 2];
        assert_eq!(clause_lbd(&[], &decision_levels), 0);
    }

    #[test]
    fn test_lbd_negative_literals() {
        // LBD should use var_of (absolute value) for lookup.
        let decision_levels = vec![0, 1, 2, 3];
        let clause = vec![-1, -2, 3];
        assert_eq!(clause_lbd(&clause, &decision_levels), 3);
    }

    #[test]
    fn test_lbd_duplicate_levels_counted_once() {
        let decision_levels = vec![0, 2, 2, 2];
        let clause = vec![1, 2, 3];
        assert_eq!(clause_lbd(&clause, &decision_levels), 1);
    }

    // ---- Sort by activity tests ----

    #[test]
    fn test_sort_by_activity_descending() {
        let activity = vec![0.0, 1.0, 3.0, 2.0]; // var1=1.0, var2=3.0, var3=2.0
        let mut clause = vec![1, 2, 3];
        sort_by_activity(&mut clause, &activity);
        assert_eq!(clause, vec![2, 3, 1]);
    }

    #[test]
    fn test_sort_by_activity_negative_literals() {
        let activity = vec![0.0, 1.0, 3.0, 2.0];
        let mut clause = vec![-1, -2, -3];
        sort_by_activity(&mut clause, &activity);
        assert_eq!(clause, vec![-2, -3, -1]);
    }

    #[test]
    fn test_sort_by_activity_equal_scores() {
        let activity = vec![0.0, 1.0, 1.0, 1.0];
        let mut clause = vec![1, 2, 3];
        sort_by_activity(&mut clause, &activity);
        // All equal: order is stable or arbitrary, but should not panic.
        assert_eq!(clause.len(), 3);
    }

    #[test]
    fn test_sort_by_activity_empty_clause() {
        let activity = vec![0.0, 1.0];
        let mut clause: Vec<i32> = Vec::new();
        sort_by_activity(&mut clause, &activity);
        assert!(clause.is_empty());
    }

    // ---- MinimizationResult struct tests ----

    #[test]
    fn test_minimization_result_construction() {
        let result = MinimizationResult {
            original_size: 5,
            minimized_size: 3,
            reduction: 2,
            sound: true,
        };
        assert_eq!(result.original_size, 5);
        assert_eq!(result.minimized_size, 3);
        assert_eq!(result.reduction, 2);
        assert!(result.sound);
    }

    #[test]
    fn test_minimization_result_clone_eq() {
        let r1 = MinimizationResult {
            original_size: 4,
            minimized_size: 2,
            reduction: 2,
            sound: true,
        };
        let r2 = r1.clone();
        assert_eq!(r1, r2);
    }

    // ---- Proof status constants ----

    #[test]
    fn test_proof_status_constants() {
        assert_eq!(S09_SELF_SUBSUMPTION_SOUND, ProofStatus::DerivedPending);
        assert_eq!(
            S10_VIVIFICATION_PRESERVES_ENTAILMENT,
            ProofStatus::DerivedPending
        );
    }

    // ---- Integration tests ----

    #[test]
    fn test_end_to_end_minimize_and_verify() {
        let learned = vec![1, 2, 3];
        let db = vec![vec![-1, 2]];
        let minimized = minimize_learned_clause(&learned, &db);
        assert!(minimized.len() < learned.len());
        assert!(verify_minimization_sound(&learned, &minimized, 3));
    }

    #[test]
    fn test_lbd_after_minimization() {
        let decision_levels = vec![0, 1, 2, 3]; // var1@1, var2@2, var3@3
        let original = vec![1, 2, 3];
        assert_eq!(clause_lbd(&original, &decision_levels), 3);

        // After minimization removes var 1, LBD decreases.
        let db = vec![vec![-1, 2]];
        let minimized = minimize_learned_clause(&original, &db);
        let new_lbd = clause_lbd(&minimized, &decision_levels);
        assert!(new_lbd <= 3);
    }
}
