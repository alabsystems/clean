// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for VSIDS decision heuristic.

#[cfg(test)]
mod tests {
    use crate::sat_verify::cdcl::vsids::{
        VsidsScores, VSIDS_DECAY_PRESERVES_ORDER, VSIDS_ORDERING_CONSISTENT,
        VSIDS_RESCALE_PRESERVES_ORDER,
    };
    use crate::sat_verify::cdcl::AssignValue;
    use crate::spec::ProofStatus;

    fn unassigned(n: u32) -> Vec<Option<AssignValue>> {
        vec![None; (n + 1) as usize]
    }

    // ---- Construction tests ----

    #[test]
    fn test_vsids_new_initial_scores_zero() {
        let scores = VsidsScores::new(5, 0.95);
        for var in 1..=5 {
            assert_eq!(scores.activity(var), 0.0, "var {var} should start at 0");
        }
    }

    #[test]
    fn test_vsids_num_vars() {
        let scores = VsidsScores::new(10, 0.95);
        assert_eq!(scores.num_vars(), 10);
    }

    #[test]
    #[should_panic(expected = "decay_factor must be in (0, 1)")]
    fn test_vsids_invalid_decay_zero() {
        let _ = VsidsScores::new(5, 0.0);
    }

    #[test]
    #[should_panic(expected = "decay_factor must be in (0, 1)")]
    fn test_vsids_invalid_decay_one() {
        let _ = VsidsScores::new(5, 1.0);
    }

    #[test]
    #[should_panic(expected = "decay_factor must be in (0, 1)")]
    fn test_vsids_invalid_decay_negative() {
        let _ = VsidsScores::new(5, -0.5);
    }

    // ---- Bump tests ----

    #[test]
    fn test_vsids_bump_increases_activity() {
        let mut scores = VsidsScores::new(3, 0.95);
        assert_eq!(scores.activity(1), 0.0);
        scores.bump(1);
        assert!(scores.activity(1) > 0.0);
    }

    #[test]
    fn test_vsids_bump_multiple_accumulates() {
        let mut scores = VsidsScores::new(3, 0.95);
        scores.bump(2);
        let after_one = scores.activity(2);
        scores.bump(2);
        let after_two = scores.activity(2);
        assert!(
            after_two > after_one,
            "second bump should increase activity"
        );
    }

    #[test]
    fn test_vsids_bump_out_of_range_no_panic() {
        let mut scores = VsidsScores::new(3, 0.95);
        // Bumping a variable beyond range should not panic.
        scores.bump(100);
        assert_eq!(scores.activity(100), 0.0);
    }

    // ---- Decay tests ----

    #[test]
    fn test_vsids_decay_makes_future_bumps_larger() {
        let mut scores = VsidsScores::new(3, 0.95);
        scores.bump(1); // bump = 1.0
        let act1 = scores.activity(1);

        scores.decay(); // bump = 1.0/0.95 ~= 1.053
        scores.bump(2);
        let act2 = scores.activity(2);

        assert!(
            act2 > act1,
            "bump after decay should be larger: {act2} vs {act1}"
        );
    }

    #[test]
    fn test_vsids_decay_relative_ordering() {
        let mut scores = VsidsScores::new(3, 0.95);
        scores.bump(1);
        scores.bump(1);
        scores.bump(2);

        assert!(scores.activity(1) > scores.activity(2));

        // After decay, relative ordering is preserved.
        scores.decay();

        // Bumping neither changes relative ordering.
        // (Activity values don't change -- only bump_amount changes.)
        assert!(scores.activity(1) > scores.activity(2));
    }

    #[test]
    fn test_vsids_many_decays_bump_grows() {
        let mut scores = VsidsScores::new(3, 0.95);
        // After 100 decays, the bump amount should be much larger.
        for _ in 0..100 {
            scores.decay();
        }
        scores.bump(1);
        // 1.0 / 0.95^100 ~= 131.5
        assert!(
            scores.activity(1) > 100.0,
            "after 100 decays, bump should be large: {}",
            scores.activity(1)
        );
    }

    // ---- Pick decision tests ----

    #[test]
    fn test_vsids_pick_decision_all_equal() {
        let scores = VsidsScores::new(3, 0.95);
        let assignment = unassigned(3);
        // All scores are 0 -- should pick some variable (implementation picks first).
        let picked = scores.pick_decision(&assignment);
        assert!(picked.is_some());
        let v = picked.unwrap();
        assert!((1..=3).contains(&v));
    }

    #[test]
    fn test_vsids_pick_decision_highest_activity() {
        let mut scores = VsidsScores::new(5, 0.95);
        scores.bump(3);
        scores.bump(3);
        scores.bump(1);

        let assignment = unassigned(5);
        let picked = scores.pick_decision(&assignment).expect("should pick");
        assert_eq!(picked, 3, "should pick var 3 with highest activity");
    }

    #[test]
    fn test_vsids_pick_decision_skips_assigned() {
        let mut scores = VsidsScores::new(3, 0.95);
        scores.bump(1);
        scores.bump(1);
        scores.bump(2);

        let mut assignment = unassigned(3);
        assignment[1] = Some(AssignValue::True); // var 1 assigned

        let picked = scores.pick_decision(&assignment).expect("should pick");
        assert_eq!(picked, 2, "should skip assigned var 1, pick var 2");
    }

    #[test]
    fn test_vsids_pick_decision_all_assigned_returns_none() {
        let scores = VsidsScores::new(2, 0.95);
        let mut assignment = unassigned(2);
        assignment[1] = Some(AssignValue::True);
        assignment[2] = Some(AssignValue::False);

        assert!(scores.pick_decision(&assignment).is_none());
    }

    #[test]
    fn test_vsids_pick_decision_only_one_unassigned() {
        let mut scores = VsidsScores::new(3, 0.95);
        scores.bump(1);

        let mut assignment = unassigned(3);
        assignment[1] = Some(AssignValue::True);
        assignment[2] = Some(AssignValue::False);
        // Only var 3 is unassigned.

        let picked = scores.pick_decision(&assignment).expect("should pick");
        assert_eq!(picked, 3);
    }

    // ---- Rescaling tests ----

    #[test]
    fn test_vsids_rescale_preserves_ordering() {
        let mut scores = VsidsScores::new(3, 0.95);
        // Force very high bump amounts to trigger rescaling.
        for _ in 0..1000 {
            scores.decay();
        }
        scores.bump(1);
        scores.bump(1);
        scores.bump(2);

        // Var 1 should still have higher activity than var 2 after rescale.
        assert!(
            scores.activity(1) > scores.activity(2),
            "ordering preserved after rescale: {} vs {}",
            scores.activity(1),
            scores.activity(2)
        );
    }

    #[test]
    fn test_vsids_rescale_keeps_finite() {
        let mut scores = VsidsScores::new(3, 0.95);
        // Push scores very high.
        for _ in 0..5000 {
            scores.decay();
            scores.bump(1);
        }
        // Activity should be finite (rescale prevents overflow).
        assert!(
            scores.activity(1).is_finite(),
            "activity should be finite: {}",
            scores.activity(1)
        );
    }

    // ---- Integration: bump from conflict, then pick ----

    #[test]
    fn test_vsids_integration_conflict_bump_then_pick() {
        let mut scores = VsidsScores::new(5, 0.95);

        // Simulate conflict analysis involving variables 2, 3, 5.
        let conflict_vars = [2, 3, 5];
        for &v in &conflict_vars {
            scores.bump(v);
        }
        scores.decay();

        let assignment = unassigned(5);
        let picked = scores.pick_decision(&assignment).expect("should pick");
        // Should pick one of the bumped variables.
        assert!(
            conflict_vars.contains(&picked),
            "should pick a bumped variable, got {picked}"
        );
    }

    #[test]
    fn test_vsids_integration_repeated_conflicts() {
        let mut scores = VsidsScores::new(5, 0.95);

        // Conflict 1: vars 1, 2
        scores.bump(1);
        scores.bump(2);
        scores.decay();

        // Conflict 2: vars 2, 3
        scores.bump(2);
        scores.bump(3);
        scores.decay();

        // Conflict 3: vars 2, 4
        scores.bump(2);
        scores.bump(4);
        scores.decay();

        // Var 2 participated in all 3 conflicts, should have highest score.
        let assignment = unassigned(5);
        let picked = scores.pick_decision(&assignment).expect("should pick");
        assert_eq!(picked, 2, "var 2 in all conflicts should be picked");
    }

    // ---- Proof status constants ----

    #[test]
    fn test_vsids_proof_status_constants() {
        assert_eq!(VSIDS_ORDERING_CONSISTENT, ProofStatus::DerivedPending);
        assert_eq!(VSIDS_DECAY_PRESERVES_ORDER, ProofStatus::DerivedPending);
        assert_eq!(VSIDS_RESCALE_PRESERVES_ORDER, ProofStatus::DerivedPending);
    }
}
