// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for CDCL restart strategy verification.

#[cfg(test)]
mod tests {
    use crate::sat_verify::cdcl::restart::{
        geometric_sequence, glucose_lbd_average, luby_sequence, restart_frequency_analysis,
        should_restart_glucose, should_restart_luby, verify_luby_property,
        verify_restart_preserves_clauses, RestartStats, RestartStrategy,
        S07_RESTART_PRESERVES_TRAIL_PREFIX, S08_LUBY_SEQUENCE_OPTIMAL,
    };
    use crate::spec::ProofStatus;

    // ---- Luby sequence tests ----

    /// Known Luby sequence values (0-indexed): 1,1,2,1,1,2,4,1,1,2,1,1,2,4,8,...
    const LUBY_FIRST_20: [u64; 20] = [1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, 1, 1, 2, 1, 1];

    #[test]
    fn test_luby_sequence_first_20_values() {
        for (i, &expected) in LUBY_FIRST_20.iter().enumerate() {
            assert_eq!(
                luby_sequence(i),
                expected,
                "luby_sequence({i}) = {} but expected {expected}",
                luby_sequence(i),
            );
        }
    }

    #[test]
    fn test_luby_sequence_index_zero() {
        assert_eq!(luby_sequence(0), 1);
    }

    #[test]
    fn test_luby_sequence_powers_of_two_minus_one() {
        // At indices 2^k - 2 (0-indexed), the value should be 2^(k-1).
        // i=0: 2^1-2=0 -> 2^0=1 (luby(0)=1)
        // i=2: 2^2-2=2 -> 2^1=2 (luby(2)=2)
        // i=6: 2^3-2=6 -> 2^2=4 (luby(6)=4)
        // i=14: 2^4-2=14 -> 2^3=8 (luby(14)=8)
        assert_eq!(luby_sequence(0), 1);
        assert_eq!(luby_sequence(2), 2);
        assert_eq!(luby_sequence(6), 4);
        assert_eq!(luby_sequence(14), 8);
        assert_eq!(luby_sequence(30), 16);
    }

    #[test]
    fn test_luby_sequence_self_similar_structure() {
        // The Luby sequence repeats the pattern at each power-of-two boundary.
        // luby(0..2) = [1,1,2]
        // luby(3..5) = [1,1,2] (same prefix)
        // luby(7..9) = [1,1,2] (same prefix)
        assert_eq!(luby_sequence(0), luby_sequence(3));
        assert_eq!(luby_sequence(1), luby_sequence(4));
        assert_eq!(luby_sequence(2), luby_sequence(5));
        assert_eq!(luby_sequence(0), luby_sequence(7));
        assert_eq!(luby_sequence(1), luby_sequence(8));
    }

    #[test]
    fn test_luby_sequence_large_index() {
        // Index 62 = 2^6 - 2, should be 2^5 = 32
        assert_eq!(luby_sequence(62), 32);
    }

    // ---- Geometric sequence tests ----

    #[test]
    fn test_geometric_sequence_base_case() {
        assert_eq!(geometric_sequence(100, 1.5, 0), 100);
    }

    #[test]
    fn test_geometric_sequence_growth() {
        // 100 * 1.5^1 = 150
        assert_eq!(geometric_sequence(100, 1.5, 1), 150);
        // 100 * 1.5^2 = 225
        assert_eq!(geometric_sequence(100, 1.5, 2), 225);
    }

    #[test]
    fn test_geometric_sequence_monotonic_increase() {
        let values: Vec<u64> = (0..10).map(|i| geometric_sequence(100, 1.1, i)).collect();
        for w in values.windows(2) {
            assert!(w[1] >= w[0], "geometric sequence should be non-decreasing");
        }
    }

    #[test]
    fn test_geometric_sequence_saturation() {
        // Very large exponent should saturate at u64::MAX.
        let result = geometric_sequence(1000, 2.0, 100);
        assert_eq!(result, u64::MAX);
    }

    #[test]
    fn test_geometric_sequence_factor_one() {
        // factor=1.0 means constant threshold.
        for i in 0..10 {
            assert_eq!(geometric_sequence(50, 1.0, i), 50);
        }
    }

    // ---- Glucose LBD average tests ----

    #[test]
    fn test_glucose_lbd_average_simple() {
        let history = vec![3, 5, 7, 9];
        let avg = glucose_lbd_average(&history, 4);
        assert!(
            (avg - 6.0).abs() < f64::EPSILON,
            "avg should be 6.0, got {avg}"
        );
    }

    #[test]
    fn test_glucose_lbd_average_window_smaller_than_history() {
        let history = vec![10, 20, 30, 40, 50];
        let avg = glucose_lbd_average(&history, 3);
        // Last 3: 30, 40, 50 -> 40.0
        assert!(
            (avg - 40.0).abs() < f64::EPSILON,
            "avg of last 3 should be 40.0, got {avg}"
        );
    }

    #[test]
    fn test_glucose_lbd_average_window_larger_than_history() {
        let history = vec![4, 6];
        let avg = glucose_lbd_average(&history, 100);
        assert!(
            (avg - 5.0).abs() < f64::EPSILON,
            "should use entire history"
        );
    }

    #[test]
    fn test_glucose_lbd_average_empty_history() {
        assert_eq!(glucose_lbd_average(&[], 10), 0.0);
    }

    #[test]
    fn test_glucose_lbd_average_zero_window() {
        assert_eq!(glucose_lbd_average(&[1, 2, 3], 0), 0.0);
    }

    #[test]
    fn test_glucose_lbd_average_single_element() {
        assert!((glucose_lbd_average(&[7], 1) - 7.0).abs() < f64::EPSILON);
    }

    // ---- Restart decision tests ----

    #[test]
    fn test_should_restart_luby_below_threshold() {
        // luby(0)=1, threshold = 100*1 = 100. 50 conflicts < 100.
        assert!(!should_restart_luby(50, 100, 0));
    }

    #[test]
    fn test_should_restart_luby_at_threshold() {
        // luby(0)=1, threshold = 100. Conflicts = 100.
        assert!(should_restart_luby(100, 100, 0));
    }

    #[test]
    fn test_should_restart_luby_above_threshold() {
        assert!(should_restart_luby(200, 100, 0));
    }

    #[test]
    fn test_should_restart_luby_second_restart() {
        // luby(1)=1, threshold = 100*1 = 100.
        assert!(should_restart_luby(100, 100, 1));
        assert!(!should_restart_luby(99, 100, 1));
    }

    #[test]
    fn test_should_restart_luby_third_restart_larger_threshold() {
        // luby(2)=2, threshold = 100*2 = 200.
        assert!(!should_restart_luby(199, 100, 2));
        assert!(should_restart_luby(200, 100, 2));
    }

    #[test]
    fn test_should_restart_glucose_too_few_clauses() {
        let history: Vec<u32> = (0..49).map(|i| i + 1).collect();
        // Fewer than 50 -> always false.
        assert!(!should_restart_glucose(&history, 0.8));
    }

    #[test]
    fn test_should_restart_glucose_uniform_lbd() {
        // All LBDs equal -> local_avg == global_avg -> no restart for factor > 1.0.
        let history = vec![5u32; 100];
        assert!(!should_restart_glucose(&history, 1.1));
    }

    #[test]
    fn test_should_restart_glucose_degrading_quality() {
        // Global: lots of low-LBD clauses, then recent ones are high-LBD.
        let mut history = vec![2u32; 200];
        for item in history.iter_mut().skip(180) {
            *item = 20; // Last 20 items are high-LBD.
        }
        // Local window (last 50): 30 items of LBD=2, 20 items of LBD=20.
        // Local avg = (30*2 + 20*20)/50 = (60+400)/50 = 9.2
        // Global avg = (180*2 + 20*20)/200 = (360+400)/200 = 3.8
        // 9.2 > 0.8 * 3.8 = 3.04 -> should restart.
        assert!(should_restart_glucose(&history, 0.8));
    }

    // ---- Luby property verification ----

    #[test]
    fn test_verify_luby_property_correct_sequence() {
        let seq: Vec<u64> = LUBY_FIRST_20.to_vec();
        assert!(verify_luby_property(&seq, 20));
    }

    #[test]
    fn test_verify_luby_property_partial_check() {
        let seq: Vec<u64> = (0..5).map(luby_sequence).collect();
        assert!(verify_luby_property(&seq, 5));
    }

    #[test]
    fn test_verify_luby_property_wrong_value() {
        let mut seq: Vec<u64> = LUBY_FIRST_20.to_vec();
        seq[6] = 999; // Should be 4.
        assert!(!verify_luby_property(&seq, 20));
    }

    #[test]
    fn test_verify_luby_property_empty_sequence() {
        assert!(verify_luby_property(&[], 0));
    }

    #[test]
    fn test_verify_luby_property_n_exceeds_len() {
        let seq = vec![1u64, 1, 2];
        // n=10 but only 3 elements; verifies just the 3 present.
        assert!(verify_luby_property(&seq, 10));
    }

    // ---- Clause preservation verification ----

    #[test]
    fn test_verify_restart_preserves_clauses_identical() {
        let clauses = vec![vec![1, -2, 3], vec![-1, 2]];
        assert!(verify_restart_preserves_clauses(&clauses, &clauses));
    }

    #[test]
    fn test_verify_restart_preserves_clauses_with_learned() {
        let before = vec![vec![1, -2], vec![-1, 3]];
        let mut after = before.clone();
        after.push(vec![2, 3]); // Learned clause added.
        assert!(verify_restart_preserves_clauses(&before, &after));
    }

    #[test]
    fn test_verify_restart_preserves_clauses_missing_clause() {
        let before = vec![vec![1, -2], vec![-1, 3]];
        let after = vec![vec![1, -2]]; // Missing [-1, 3].
        assert!(!verify_restart_preserves_clauses(&before, &after));
    }

    #[test]
    fn test_verify_restart_preserves_clauses_empty() {
        assert!(verify_restart_preserves_clauses(&[], &[]));
        assert!(verify_restart_preserves_clauses(&[], &[vec![1, 2]]));
    }

    // ---- Restart frequency analysis ----

    #[test]
    fn test_restart_frequency_analysis_empty() {
        let stats = restart_frequency_analysis(&[]);
        assert_eq!(stats.total_restarts, 0);
        assert_eq!(stats.mean_interval, 0.0);
    }

    #[test]
    fn test_restart_frequency_analysis_single() {
        let stats = restart_frequency_analysis(&[100]);
        assert_eq!(stats.total_restarts, 1);
        assert!((stats.mean_interval - 100.0).abs() < f64::EPSILON);
        assert!((stats.median_interval - 100.0).abs() < f64::EPSILON);
        assert_eq!(stats.max_interval, 100);
    }

    #[test]
    fn test_restart_frequency_analysis_uniform_intervals() {
        // Restarts at conflicts 100, 200, 300, 400.
        let stats = restart_frequency_analysis(&[100, 200, 300, 400]);
        assert_eq!(stats.total_restarts, 4);
        assert!((stats.mean_interval - 100.0).abs() < f64::EPSILON);
        assert!((stats.median_interval - 100.0).abs() < f64::EPSILON);
        assert_eq!(stats.max_interval, 100);
    }

    #[test]
    fn test_restart_frequency_analysis_varying_intervals() {
        // Intervals: 10, 20, 30, 40, 50
        let counts = vec![10, 30, 60, 100, 150];
        let stats = restart_frequency_analysis(&counts);
        assert_eq!(stats.total_restarts, 5);
        // Intervals: 10, 20, 30, 40, 50 -> mean = 30.0
        assert!((stats.mean_interval - 30.0).abs() < f64::EPSILON);
        // Sorted: [10, 20, 30, 40, 50] -> median = 30
        assert!((stats.median_interval - 30.0).abs() < f64::EPSILON);
        assert_eq!(stats.max_interval, 50);
    }

    #[test]
    fn test_restart_frequency_analysis_even_count_median() {
        // Intervals: 10, 30, 20, 40 (from counts 10, 40, 60, 100)
        let stats = restart_frequency_analysis(&[10, 40, 60, 100]);
        // Intervals: 10, 30, 20, 40 -> sorted: [10, 20, 30, 40] -> median = (20+30)/2 = 25
        assert!(
            (stats.median_interval - 25.0).abs() < f64::EPSILON,
            "median should be 25.0, got {}",
            stats.median_interval
        );
    }

    // ---- Enum and struct construction tests ----

    #[test]
    fn test_restart_strategy_enum_variants() {
        let luby = RestartStrategy::Luby { unit: 100 };
        let geo = RestartStrategy::Geometric {
            base: 100,
            factor: 1.5,
        };
        let glucose = RestartStrategy::Glucose {
            threshold_factor: 0.8,
        };
        // Verify each variant is distinct.
        assert_ne!(luby, geo);
        assert_ne!(geo, glucose);
        assert_ne!(luby, glucose);
    }

    #[test]
    fn test_restart_stats_fields() {
        let stats = RestartStats {
            total_restarts: 42,
            mean_interval: 150.5,
            median_interval: 120.0,
            max_interval: 500,
        };
        assert_eq!(stats.total_restarts, 42);
        assert!((stats.mean_interval - 150.5).abs() < f64::EPSILON);
        assert!((stats.median_interval - 120.0).abs() < f64::EPSILON);
        assert_eq!(stats.max_interval, 500);
    }

    // ---- Proof status constants ----

    #[test]
    fn test_restart_proof_status_constants() {
        assert_eq!(
            S07_RESTART_PRESERVES_TRAIL_PREFIX,
            ProofStatus::DerivedPending
        );
        assert_eq!(S08_LUBY_SEQUENCE_OPTIMAL, ProofStatus::DerivedPending);
    }
}
