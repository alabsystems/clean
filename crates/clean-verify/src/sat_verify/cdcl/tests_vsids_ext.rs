// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended VSIDS verification: decay, phase saving, Luby restarts.

#[cfg(test)]
mod tests {
    use crate::sat_verify::cdcl::vsids_extensions::{
        luby_restart_sequence, phase_saving_consistency, rescale_scores, verify_bump_ordering,
        verify_decay_monotonicity, verify_restart_schedule, verify_score_overflow_safety,
        S07_VSIDS_DECAY_MONOTONICITY, S08_PHASE_SAVING_CONSISTENCY,
    };
    use crate::spec::ProofStatus;

    // ==== Decay monotonicity ====

    #[test]
    fn test_decay_monotonicity_basic() {
        let before = vec![10.0, 20.0, 30.0];
        let factor = 0.95;
        let after: Vec<f64> = before.iter().map(|&s| s * factor).collect();
        assert!(verify_decay_monotonicity(&before, &after, factor));
    }

    #[test]
    fn test_decay_monotonicity_zero_decay() {
        // decay_factor = 0.0 is out of range (0,1] — should fail.
        let before = vec![10.0, 20.0];
        let after = vec![0.0, 0.0];
        assert!(!verify_decay_monotonicity(&before, &after, 0.0));
    }

    #[test]
    fn test_decay_monotonicity_full_decay_factor_one() {
        // decay_factor = 1.0 means no change — scores stay the same.
        let before = vec![5.0, 15.0, 25.0];
        let after = before.clone();
        assert!(verify_decay_monotonicity(&before, &after, 1.0));
    }

    #[test]
    fn test_decay_monotonicity_mismatched_lengths() {
        let before = vec![10.0, 20.0];
        let after = vec![9.5];
        assert!(!verify_decay_monotonicity(&before, &after, 0.95));
    }

    #[test]
    fn test_decay_monotonicity_empty_scores() {
        let empty: Vec<f64> = vec![];
        assert!(verify_decay_monotonicity(&empty, &empty, 0.95));
    }

    #[test]
    fn test_decay_monotonicity_wrong_values_rejected() {
        let before = vec![10.0, 20.0];
        // after[1] is wrong — should be 19.0 not 21.0.
        let after = vec![9.5, 21.0];
        assert!(!verify_decay_monotonicity(&before, &after, 0.95));
    }

    #[test]
    fn test_decay_monotonicity_all_zero_scores() {
        let before = vec![0.0, 0.0, 0.0];
        let after = vec![0.0, 0.0, 0.0];
        assert!(verify_decay_monotonicity(&before, &after, 0.5));
    }

    #[test]
    fn test_decay_monotonicity_negative_factor_rejected() {
        let before = vec![10.0];
        let after = vec![-5.0];
        assert!(!verify_decay_monotonicity(&before, &after, -0.5));
    }

    // ==== Bump ordering ====

    #[test]
    fn test_bump_ordering_single_bumped() {
        // Var 2 was bumped and has highest score.
        let scores = vec![1.0, 2.0, 10.0, 3.0];
        assert!(verify_bump_ordering(&scores, &[2]));
    }

    #[test]
    fn test_bump_ordering_multiple_bumped() {
        let scores = vec![1.0, 2.0, 10.0, 8.0, 3.0];
        // Vars 2 and 3 bumped: min(10.0, 8.0) = 8.0 >= max(1.0, 2.0, 3.0) = 3.0.
        assert!(verify_bump_ordering(&scores, &[2, 3]));
    }

    #[test]
    fn test_bump_ordering_all_bumped() {
        let scores = vec![5.0, 3.0, 7.0];
        assert!(verify_bump_ordering(&scores, &[0, 1, 2]));
    }

    #[test]
    fn test_bump_ordering_violation() {
        // Var 1 bumped but score 2.0 < non-bumped var 2 score 10.0.
        let scores = vec![1.0, 2.0, 10.0];
        assert!(!verify_bump_ordering(&scores, &[1]));
    }

    #[test]
    fn test_bump_ordering_empty_scores() {
        let scores: Vec<f64> = vec![];
        assert!(verify_bump_ordering(&scores, &[0]));
    }

    #[test]
    fn test_bump_ordering_empty_bumped() {
        let scores = vec![1.0, 2.0, 3.0];
        assert!(verify_bump_ordering(&scores, &[]));
    }

    #[test]
    fn test_bump_ordering_equal_scores() {
        // Bumped and non-bumped have the same score — should pass (>=).
        let scores = vec![5.0, 5.0, 5.0];
        assert!(verify_bump_ordering(&scores, &[0]));
    }

    // ==== Score overflow safety ====

    #[test]
    fn test_overflow_safety_all_safe() {
        let scores = vec![1.0, 50.0, 99.9];
        assert!(verify_score_overflow_safety(&scores, 100.0));
    }

    #[test]
    fn test_overflow_safety_at_boundary() {
        let scores = vec![100.0];
        assert!(verify_score_overflow_safety(&scores, 100.0));
    }

    #[test]
    fn test_overflow_safety_violation() {
        let scores = vec![1.0, 200.0, 3.0];
        assert!(!verify_score_overflow_safety(&scores, 100.0));
    }

    #[test]
    fn test_overflow_safety_negative_score_rejected() {
        let scores = vec![-1.0, 5.0];
        assert!(!verify_score_overflow_safety(&scores, 100.0));
    }

    #[test]
    fn test_overflow_safety_empty() {
        let scores: Vec<f64> = vec![];
        assert!(verify_score_overflow_safety(&scores, 100.0));
    }

    // ==== Rescaling ====

    #[test]
    fn test_rescale_basic() {
        let mut scores = vec![100.0, 200.0, 300.0];
        rescale_scores(&mut scores, 0.5);
        assert_eq!(scores, vec![50.0, 100.0, 150.0]);
    }

    #[test]
    fn test_rescale_preserves_ordering() {
        let mut scores = vec![10.0, 30.0, 20.0];
        rescale_scores(&mut scores, 0.1);
        assert!(scores[1] > scores[2]);
        assert!(scores[2] > scores[0]);
    }

    #[test]
    fn test_rescale_zero_factor_noop() {
        let mut scores = vec![10.0, 20.0];
        let original = scores.clone();
        rescale_scores(&mut scores, 0.0);
        assert_eq!(scores, original, "zero factor should be a no-op");
    }

    #[test]
    fn test_rescale_negative_factor_noop() {
        let mut scores = vec![10.0, 20.0];
        let original = scores.clone();
        rescale_scores(&mut scores, -1.0);
        assert_eq!(scores, original, "negative factor should be a no-op");
    }

    #[test]
    fn test_rescale_infinity_factor_noop() {
        let mut scores = vec![10.0, 20.0];
        let original = scores.clone();
        rescale_scores(&mut scores, f64::INFINITY);
        assert_eq!(scores, original, "infinite factor should be a no-op");
    }

    #[test]
    fn test_rescale_empty() {
        let mut scores: Vec<f64> = vec![];
        rescale_scores(&mut scores, 0.5);
        assert!(scores.is_empty());
    }

    // ==== Phase saving consistency ====

    #[test]
    fn test_phase_saving_consistent() {
        // Var 0 last assigned positive, var 1 last assigned negative.
        let _saved = [Some(true), Some(false)];
        let _trail = [(1, true), (-2, false)]; // var 1 = true (lit 1), var 2 = false (lit -2)
                                               // saved_phases[0] = Some(true) matches var 0 — but var 0 not on trail? Actually
                                               // lit=1 means var=1, and saved_phases is 0-indexed...
                                               // Let me be precise: saved_phases[0] for var 0, saved_phases[1] for var 1.
                                               // trail: (1, true) means lit=1, var=1, pol=positive(true).
                                               //        (-2, false) means lit=-2, var=2, pol=negative(false).
                                               // So var 0 has no trail entry, but saved_phases[0] = Some(true) => inconsistent.
                                               // Let me fix the test to be correct.
        let saved_correct = vec![None, Some(true), Some(false)];
        let trail_correct = vec![(1, true), (-2, false)];
        assert!(phase_saving_consistency(&saved_correct, &trail_correct));
    }

    #[test]
    fn test_phase_saving_missing_trail_entry() {
        // Saved phase exists for var 5, but var 5 never on trail.
        let mut saved = vec![None; 6];
        saved[5] = Some(true);
        let trail: Vec<(i32, bool)> = vec![(1, true)]; // only var 1 on trail
        assert!(!phase_saving_consistency(&saved, &trail));
    }

    #[test]
    fn test_phase_saving_conflict_wrong_polarity() {
        // Var 1 was last assigned negative, but saved phase says positive.
        let saved = vec![None, Some(true)];
        let trail = vec![(-1, false)]; // var 1 negative
        assert!(!phase_saving_consistency(&saved, &trail));
    }

    #[test]
    fn test_phase_saving_multiple_assignments_last_wins() {
        // Var 1 assigned positive, then backtracked and assigned negative.
        // The last occurrence on the trail determines the expected polarity.
        let saved = vec![None, Some(false)];
        let trail = vec![(1, true), (-1, false)]; // last: var 1 negative
        assert!(phase_saving_consistency(&saved, &trail));
    }

    #[test]
    fn test_phase_saving_all_none_consistent() {
        let saved = vec![None, None, None];
        let trail = vec![(1, true), (-2, false)];
        assert!(phase_saving_consistency(&saved, &trail));
    }

    #[test]
    fn test_phase_saving_empty_trail_and_saved() {
        let saved: Vec<Option<bool>> = vec![];
        let trail: Vec<(i32, bool)> = vec![];
        assert!(phase_saving_consistency(&saved, &trail));
    }

    #[test]
    fn test_phase_saving_empty_trail_with_saved_phases() {
        // Saved phase exists but trail is empty => inconsistent.
        let saved = vec![Some(true)];
        let trail: Vec<(i32, bool)> = vec![];
        assert!(!phase_saving_consistency(&saved, &trail));
    }

    // ==== Luby restart sequence ====

    #[test]
    fn test_luby_first_20_values() {
        // Known Luby sequence: 1,1,2,1,1,2,4,1,1,2,1,1,2,4,8,1,1,2,1,1
        let expected: Vec<u64> = vec![1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, 1, 1, 2, 1, 1];
        for (i, &exp) in expected.iter().enumerate() {
            assert_eq!(
                luby_restart_sequence(i),
                exp,
                "luby({i}) should be {exp}, got {}",
                luby_restart_sequence(i)
            );
        }
    }

    #[test]
    fn test_luby_power_of_two_positions() {
        // At positions 2^k - 2 (0-indexed), the Luby value is 2^(k-1).
        // pos 0: luby = 1 = 2^0
        // pos 2: luby = 2 = 2^1
        // pos 6: luby = 4 = 2^2
        // pos 14: luby = 8 = 2^3
        // pos 30: luby = 16 = 2^4
        assert_eq!(luby_restart_sequence(0), 1);
        assert_eq!(luby_restart_sequence(2), 2);
        assert_eq!(luby_restart_sequence(6), 4);
        assert_eq!(luby_restart_sequence(14), 8);
        assert_eq!(luby_restart_sequence(30), 16);
    }

    #[test]
    fn test_luby_sequence_pattern_repeats() {
        // The prefix [1,1,2] repeats at positions 0..3, 3..6, 7..10, etc.
        assert_eq!(luby_restart_sequence(0), 1);
        assert_eq!(luby_restart_sequence(1), 1);
        assert_eq!(luby_restart_sequence(2), 2);
        assert_eq!(luby_restart_sequence(3), 1);
        assert_eq!(luby_restart_sequence(4), 1);
        assert_eq!(luby_restart_sequence(5), 2);
        assert_eq!(luby_restart_sequence(6), 4);
    }

    #[test]
    fn test_luby_large_index() {
        // Index 62 = 2^6 - 2, should give 2^5 = 32.
        assert_eq!(luby_restart_sequence(62), 32);
    }

    // ==== Restart schedule verification ====

    #[test]
    fn test_restart_schedule_basic() {
        let base = 100;
        let restarts: Vec<u64> = (0..7).map(|i| base * luby_restart_sequence(i)).collect();
        // Expected: 100, 100, 200, 100, 100, 200, 400
        assert!(verify_restart_schedule(&restarts, base));
    }

    #[test]
    fn test_restart_schedule_wrong_value() {
        let restarts = vec![100, 100, 200, 100, 999]; // 999 is wrong
        assert!(!verify_restart_schedule(&restarts, 100));
    }

    #[test]
    fn test_restart_schedule_empty() {
        let restarts: Vec<u64> = vec![];
        assert!(verify_restart_schedule(&restarts, 100));
    }

    #[test]
    fn test_restart_schedule_zero_base() {
        // base_conflicts = 0: only valid if restarts is empty.
        assert!(verify_restart_schedule(&[], 0));
        assert!(!verify_restart_schedule(&[0, 0], 0));
    }

    #[test]
    fn test_restart_schedule_single_entry() {
        // First entry: base * luby(0) = base * 1 = base.
        assert!(verify_restart_schedule(&[50], 50));
        assert!(!verify_restart_schedule(&[51], 50));
    }

    // ==== Edge cases ====

    #[test]
    fn test_single_variable_decay() {
        let before = vec![42.0];
        let factor = 0.8;
        let after = vec![42.0 * 0.8];
        assert!(verify_decay_monotonicity(&before, &after, factor));
    }

    #[test]
    fn test_single_variable_bump_ordering() {
        let scores = vec![5.0];
        assert!(verify_bump_ordering(&scores, &[0]));
    }

    #[test]
    fn test_overflow_safety_single_at_max() {
        let scores = vec![1e100];
        assert!(verify_score_overflow_safety(&scores, 1e100));
        assert!(!verify_score_overflow_safety(&scores, 1e99));
    }

    // ==== Proof status constants ====

    #[test]
    fn test_vsids_ext_proof_status_constants() {
        assert_eq!(S07_VSIDS_DECAY_MONOTONICITY, ProofStatus::DerivedPending);
        assert_eq!(S08_PHASE_SAVING_CONSISTENCY, ProofStatus::DerivedPending);
    }
}
