// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for CDCL termination verification (S06).

#[cfg(test)]
mod tests {
    use crate::sat_verify::cdcl::termination::{
        build_termination_witness, clause_space_size, compute_progress_metric, is_subsumed_by,
        verify_clause_uniqueness, verify_learned_clause_new, verify_monotone_growth,
        verify_no_tautological_learned, verify_subsumption_progress, verify_termination,
        ClauseSpace, TerminationWitness, S06A_CLAUSE_SPACE_FINITE, S06B_CLAUSE_UNIQUENESS,
        S06C_MONOTONE_GROWTH,
    };
    use crate::sat_verify::cdcl::{CdclState, Clause, Literal};
    use crate::spec::ProofStatus;

    // -- Clause space size --

    #[test]
    fn test_clause_space_size_zero_vars() {
        assert_eq!(clause_space_size(0), Some(1));
    }

    #[test]
    fn test_clause_space_size_one_var() {
        assert_eq!(clause_space_size(1), Some(3));
    }

    #[test]
    fn test_clause_space_size_two_vars() {
        assert_eq!(clause_space_size(2), Some(9));
    }

    #[test]
    fn test_clause_space_size_three_vars() {
        assert_eq!(clause_space_size(3), Some(27));
    }

    #[test]
    fn test_clause_space_size_ten_vars() {
        assert_eq!(clause_space_size(10), Some(59049));
    }

    #[test]
    fn test_clause_space_size_twenty_vars() {
        assert_eq!(clause_space_size(20), Some(3_486_784_401));
    }

    #[test]
    fn test_clause_space_size_overflow_large_n() {
        // 3^81 > u128::MAX
        assert!(clause_space_size(81).is_none());
    }

    #[test]
    fn test_clause_space_size_boundary_no_overflow() {
        assert!(clause_space_size(80).is_some());
    }

    // -- ClauseSpace struct --

    #[test]
    fn test_clause_space_new() {
        let space = ClauseSpace::new(3);
        assert_eq!(space.num_vars, 3);
        assert_eq!(space.max_clauses, Some(27));
        assert!(space.is_finite_representable());
    }

    #[test]
    fn test_clause_space_overflow() {
        let space = ClauseSpace::new(81);
        assert_eq!(space.num_vars, 81);
        assert!(space.max_clauses.is_none());
        assert!(!space.is_finite_representable());
    }

    // -- Clause uniqueness --

    #[test]
    fn test_clause_uniqueness_distinct() {
        let clauses: Vec<Clause> = vec![vec![1, 2], vec![1, -2], vec![-1, 2]];
        verify_clause_uniqueness(&clauses).expect("all distinct");
    }

    #[test]
    fn test_clause_uniqueness_empty_database() {
        let clauses: Vec<Clause> = vec![];
        verify_clause_uniqueness(&clauses).expect("empty is unique");
    }

    #[test]
    fn test_clause_uniqueness_single_clause() {
        let clauses: Vec<Clause> = vec![vec![1, -2, 3]];
        verify_clause_uniqueness(&clauses).expect("single clause is unique");
    }

    #[test]
    fn test_clause_uniqueness_exact_duplicates() {
        let clauses: Vec<Clause> = vec![vec![1, 2], vec![1, 2]];
        assert!(verify_clause_uniqueness(&clauses).is_err());
    }

    #[test]
    fn test_clause_uniqueness_reordered_duplicates() {
        let clauses: Vec<Clause> = vec![vec![1, 2, 3], vec![3, 1, 2]];
        assert!(verify_clause_uniqueness(&clauses).is_err());
    }

    #[test]
    fn test_clause_uniqueness_with_internal_duplicates() {
        // [1, 2, 2] normalizes to [1, 2] -- same as [2, 1]
        let clauses: Vec<Clause> = vec![vec![1, 2, 2], vec![2, 1]];
        assert!(verify_clause_uniqueness(&clauses).is_err());
    }

    #[test]
    fn test_clause_uniqueness_empty_clause_unique() {
        let clauses: Vec<Clause> = vec![vec![1, 2], vec![]];
        verify_clause_uniqueness(&clauses).expect("empty clause is distinct");
    }

    // -- Monotone growth --

    #[test]
    fn test_monotone_growth_superset() {
        let before: Vec<Clause> = vec![vec![1, 2], vec![-1, 3]];
        let after: Vec<Clause> = vec![vec![1, 2], vec![-1, 3], vec![2, -3]];
        verify_monotone_growth(&before, &after).expect("after is superset");
    }

    #[test]
    fn test_monotone_growth_identical() {
        let before: Vec<Clause> = vec![vec![1, 2], vec![-1, 3]];
        let after: Vec<Clause> = vec![vec![1, 2], vec![-1, 3]];
        verify_monotone_growth(&before, &after).expect("identical is superset");
    }

    #[test]
    fn test_monotone_growth_empty_before() {
        let before: Vec<Clause> = vec![];
        let after: Vec<Clause> = vec![vec![1, 2]];
        verify_monotone_growth(&before, &after).expect("empty before always ok");
    }

    #[test]
    fn test_monotone_growth_fails_missing_clause() {
        let before: Vec<Clause> = vec![vec![1, 2], vec![-1, 3]];
        let after: Vec<Clause> = vec![vec![1, 2], vec![2, -3]];
        assert!(verify_monotone_growth(&before, &after).is_err());
    }

    #[test]
    fn test_monotone_growth_reordered_clauses() {
        let before: Vec<Clause> = vec![vec![1, 2], vec![-1, 3]];
        let after: Vec<Clause> = vec![vec![-1, 3], vec![1, 2]];
        verify_monotone_growth(&before, &after).expect("reordered is still superset");
    }

    // -- Progress metric --

    #[test]
    fn test_progress_metric_empty_database() {
        let clauses: Vec<Clause> = vec![];
        let progress = compute_progress_metric(&clauses, 2).expect("no overflow");
        assert!((progress - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_progress_metric_one_clause() {
        let clauses: Vec<Clause> = vec![vec![1, 2]];
        let progress = compute_progress_metric(&clauses, 2).expect("no overflow");
        assert!((progress - 1.0 / 9.0).abs() < 1e-10);
    }

    #[test]
    fn test_progress_metric_increases_with_clauses() {
        let clauses1: Vec<Clause> = vec![vec![1]];
        let clauses2: Vec<Clause> = vec![vec![1], vec![-1]];
        let p1 = compute_progress_metric(&clauses1, 1).expect("no overflow");
        let p2 = compute_progress_metric(&clauses2, 1).expect("no overflow");
        assert!(p2 > p1, "progress must increase: {p2} > {p1}");
    }

    #[test]
    fn test_progress_metric_zero_vars() {
        let clauses: Vec<Clause> = vec![vec![]];
        let progress = compute_progress_metric(&clauses, 0).expect("no overflow");
        assert!((progress - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_progress_metric_overflow_returns_none() {
        let clauses: Vec<Clause> = vec![vec![1]];
        assert!(compute_progress_metric(&clauses, 81).is_none());
    }

    #[test]
    fn test_progress_metric_duplicate_clauses_not_double_counted() {
        let clauses: Vec<Clause> = vec![vec![1, 2], vec![2, 1]];
        let progress = compute_progress_metric(&clauses, 2).expect("no overflow");
        assert!((progress - 1.0 / 9.0).abs() < 1e-10);
    }

    // -- Learned clause newness --

    #[test]
    fn test_learned_clause_new_passes() {
        let existing: Vec<Clause> = vec![vec![1, 2], vec![-1, 3]];
        verify_learned_clause_new(&existing, &[2, -3]).expect("new clause");
    }

    #[test]
    fn test_learned_clause_new_exact_duplicate() {
        let existing: Vec<Clause> = vec![vec![1, 2], vec![-1, 3]];
        assert!(verify_learned_clause_new(&existing, &[1, 2]).is_err());
    }

    #[test]
    fn test_learned_clause_new_reordered_duplicate() {
        let existing: Vec<Clause> = vec![vec![1, 2, 3]];
        assert!(verify_learned_clause_new(&existing, &[3, 1, 2]).is_err());
    }

    #[test]
    fn test_learned_clause_new_empty_database() {
        let existing: Vec<Clause> = vec![];
        verify_learned_clause_new(&existing, &[1, -2]).expect("empty db => always new");
    }

    // -- Tautological clause detection --

    #[test]
    fn test_no_tautological_normal_clause() {
        verify_no_tautological_learned(&[1, 2, 3]).expect("not tautological");
    }

    #[test]
    fn test_no_tautological_detects_tautology() {
        assert!(verify_no_tautological_learned(&[1, -1, 2]).is_err());
    }

    #[test]
    fn test_no_tautological_empty_clause() {
        verify_no_tautological_learned(&[]).expect("empty is not tautological");
    }

    #[test]
    fn test_no_tautological_single_literal() {
        verify_no_tautological_learned(&[5]).expect("single lit not tautological");
    }

    #[test]
    fn test_no_tautological_multiple_complementary_pairs() {
        assert!(verify_no_tautological_learned(&[1, -1, 2, -2]).is_err());
    }

    // -- Subsumption --

    #[test]
    fn test_subsumption_shorter_subsumes_longer() {
        assert!(is_subsumed_by(&[1, 2], &[1, 2, 3]));
    }

    #[test]
    fn test_subsumption_equal_clauses() {
        assert!(is_subsumed_by(&[1, 2], &[1, 2]));
    }

    #[test]
    fn test_subsumption_no_subsumption() {
        assert!(!is_subsumed_by(&[1, 4], &[1, 2, 3]));
    }

    #[test]
    fn test_subsumption_empty_subsumes_everything() {
        assert!(is_subsumed_by(&[], &[1, 2, 3]));
    }

    #[test]
    fn test_subsumption_nothing_subsumes_empty() {
        assert!(!is_subsumed_by(&[1], &[]));
    }

    #[test]
    fn test_subsumption_reordered() {
        assert!(is_subsumed_by(&[3, 1], &[1, 2, 3]));
    }

    #[test]
    fn test_subsumption_progress_indices() {
        let existing: Vec<Clause> = vec![vec![1, 2, 3], vec![-1, 2], vec![1, 2, 4]];
        let candidate: Vec<Literal> = vec![1, 2];
        let subsumed = verify_subsumption_progress(&existing, &candidate);
        assert_eq!(subsumed, vec![0, 2]);
    }

    #[test]
    fn test_subsumption_progress_no_subsumption() {
        let existing: Vec<Clause> = vec![vec![1, 2], vec![-1, 3]];
        let candidate: Vec<Literal> = vec![4, 5];
        let subsumed = verify_subsumption_progress(&existing, &candidate);
        assert!(subsumed.is_empty());
    }

    #[test]
    fn test_subsumption_progress_excludes_self() {
        let existing: Vec<Clause> = vec![vec![1, 2], vec![1, 2, 3]];
        let candidate: Vec<Literal> = vec![1, 2];
        let subsumed = verify_subsumption_progress(&existing, &candidate);
        assert_eq!(subsumed, vec![1]);
    }

    // -- Build termination witness --

    #[test]
    fn test_build_witness_empty_state() {
        let state = CdclState::new(3, vec![]);
        let witness = build_termination_witness(&state);
        assert_eq!(witness.unique_clause_count, 0);
        assert_eq!(witness.max_clauses, Some(27));
        assert!(!witness.has_empty_clause);
        assert!(witness.all_unique);
        assert!(witness.is_valid());
    }

    #[test]
    fn test_build_witness_with_clauses() {
        let state = CdclState::new(2, vec![vec![1, 2], vec![-1, 2], vec![-1, -2]]);
        let witness = build_termination_witness(&state);
        assert_eq!(witness.unique_clause_count, 3);
        assert_eq!(witness.max_clauses, Some(9));
        assert!(!witness.has_empty_clause);
        assert!(witness.all_unique);
    }

    #[test]
    fn test_build_witness_with_empty_clause() {
        let state = CdclState::new(2, vec![vec![1, 2], vec![]]);
        let witness = build_termination_witness(&state);
        assert!(witness.has_empty_clause);
        assert_eq!(witness.unique_clause_count, 2);
    }

    #[test]
    fn test_build_witness_with_duplicates() {
        let state = CdclState::new(2, vec![vec![1, 2], vec![2, 1]]);
        let witness = build_termination_witness(&state);
        assert!(!witness.all_unique);
        assert!(!witness.is_valid());
        assert_eq!(witness.unique_clause_count, 1);
    }

    #[test]
    fn test_witness_progress() {
        let state = CdclState::new(2, vec![vec![1, 2], vec![-1, 2]]);
        let witness = build_termination_witness(&state);
        let progress = witness.progress().expect("representable");
        assert!((progress - 2.0 / 9.0).abs() < 1e-10);
    }

    // -- Full termination verification --

    #[test]
    fn test_verify_termination_simple_ok() {
        let state = CdclState::new(2, vec![vec![1, 2], vec![-1, 2]]);
        let witness = verify_termination(&state, None).expect("valid");
        assert!(witness.is_valid());
        assert_eq!(witness.unique_clause_count, 2);
    }

    #[test]
    fn test_verify_termination_with_monotone_growth() {
        let prev = CdclState::new(2, vec![vec![1, 2]]);
        let curr = CdclState::new(2, vec![vec![1, 2], vec![-1, -2]]);
        let witness = verify_termination(&curr, Some(&prev)).expect("valid");
        assert!(witness.is_valid());
    }

    #[test]
    fn test_verify_termination_fails_duplicate() {
        let state = CdclState::new(2, vec![vec![1, 2], vec![2, 1]]);
        assert!(verify_termination(&state, None).is_err());
    }

    #[test]
    fn test_verify_termination_fails_non_monotone() {
        let prev = CdclState::new(2, vec![vec![1, 2], vec![-1, 3]]);
        let curr = CdclState::new(2, vec![vec![1, 2]]);
        assert!(verify_termination(&curr, Some(&prev)).is_err());
    }

    #[test]
    fn test_verify_termination_empty_database() {
        let state = CdclState::new(2, vec![]);
        let witness = verify_termination(&state, None).expect("valid");
        assert!(witness.is_valid());
        assert_eq!(witness.unique_clause_count, 0);
    }

    #[test]
    fn test_verify_termination_single_clause() {
        let state = CdclState::new(1, vec![vec![1]]);
        let witness = verify_termination(&state, None).expect("valid");
        assert_eq!(witness.max_clauses, Some(3));
        assert_eq!(witness.unique_clause_count, 1);
    }

    // -- Proof status constants --

    #[test]
    fn test_proof_status_s06a() {
        assert_eq!(S06A_CLAUSE_SPACE_FINITE, ProofStatus::DerivedPending);
    }

    #[test]
    fn test_proof_status_s06b() {
        assert_eq!(S06B_CLAUSE_UNIQUENESS, ProofStatus::DerivedPending);
    }

    #[test]
    fn test_proof_status_s06c() {
        assert_eq!(S06C_MONOTONE_GROWTH, ProofStatus::DerivedPending);
    }

    // -- Edge cases --

    #[test]
    fn test_all_possible_clauses_one_var() {
        // 3^1 = 3 clauses: [1], [-1], []
        let state = CdclState::new(1, vec![vec![1], vec![-1], vec![]]);
        let witness = verify_termination(&state, None).expect("valid");
        let progress = witness.progress().expect("representable");
        assert!(
            (progress - 1.0).abs() < f64::EPSILON,
            "all clauses exhausted"
        );
        assert!(witness.has_empty_clause);
    }

    #[test]
    fn test_witness_progress_overflow_returns_none() {
        let witness = TerminationWitness {
            unique_clause_count: 1,
            max_clauses: None,
            has_empty_clause: false,
            all_unique: true,
        };
        assert!(witness.progress().is_none());
        assert!(!witness.is_valid());
    }

    #[test]
    fn test_monotone_growth_reordered_literals_within_clause() {
        let before: Vec<Clause> = vec![vec![3, 1]];
        let after: Vec<Clause> = vec![vec![1, 3]];
        verify_monotone_growth(&before, &after).expect("normalized match");
    }

    #[test]
    fn test_verify_termination_previous_none() {
        let state = CdclState::new(2, vec![vec![1, -2]]);
        let witness = verify_termination(&state, None).expect("valid without previous");
        assert!(witness.is_valid());
    }
}
