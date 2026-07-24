// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for decision heuristic verification.

use super::decision_heuristic::{
    compare_heuristics, compute_decision_rate, verify_activity_monotone, verify_branching_complete,
    verify_decay_bounded, verify_decision_completeness, verify_decision_soundness,
    verify_phase_saving_consistent, verify_restart_preserves_heuristic, verify_satisfying_trace,
    verify_valid_ordering, HeuristicComparison, HeuristicProperty, S07A_DECISION_COMPLETENESS,
    S07B_DECISION_SOUNDNESS, S07C_ACTIVITY_BOUNDED,
};
use super::vsids::VsidsScores;
use super::{AssignValue, CdclState, TrailEntry};
use crate::spec::ProofStatus;

// ---- Decision completeness ----

#[test]
fn test_completeness_all_vars_on_trail() {
    let mut s = CdclState::new(3, vec![vec![1, 2], vec![-1, 3]]);
    s.decide(1).unwrap();
    s.assign(2, Some(0)).unwrap();
    s.assign(3, Some(1)).unwrap();
    verify_decision_completeness(&s).expect("all 3 vars on trail");
}

#[test]
fn test_completeness_missing_variable_fails() {
    let mut s = CdclState::new(3, vec![vec![1, 2, 3]]);
    s.decide(1).unwrap();
    s.assign(2, Some(0)).unwrap();
    assert!(
        verify_decision_completeness(&s).is_err(),
        "var 3 not on trail"
    );
}

#[test]
fn test_completeness_empty_trail_fails() {
    assert!(verify_decision_completeness(&CdclState::new(2, vec![vec![1, -2]])).is_err());
}

#[test]
fn test_completeness_single_variable() {
    let mut s = CdclState::new(1, vec![vec![1]]);
    s.decide(1).unwrap();
    verify_decision_completeness(&s).expect("single var complete");
}

#[test]
fn test_completeness_negative_literal_counts() {
    let mut s = CdclState::new(2, vec![vec![1, -2]]);
    s.decide(-1).unwrap();
    s.assign(-2, Some(0)).unwrap();
    verify_decision_completeness(&s).expect("negative literals track vars");
}

// ---- Decision soundness ----

#[test]
fn test_soundness_valid_trace() {
    let mut s = CdclState::new(3, vec![vec![1, 2, 3], vec![-1, 2]]);
    s.decide(1).unwrap();
    s.assign(2, Some(1)).unwrap();
    verify_decision_soundness(&s).expect("valid trace");
}

#[test]
fn test_soundness_invalid_reason_clause() {
    let mut s = CdclState::new(2, vec![vec![1, -2]]);
    s.trail.push(TrailEntry {
        literal: 1,
        decision_level: 0,
        reason: Some(999),
    });
    s.assignment[1] = Some(AssignValue::True);
    assert!(verify_decision_soundness(&s).is_err());
}

#[test]
fn test_soundness_all_decisions_valid() {
    let mut s = CdclState::new(3, vec![vec![1, 2, 3]]);
    s.decide(1).unwrap();
    s.decide(2).unwrap();
    s.decide(3).unwrap();
    verify_decision_soundness(&s).expect("pure decisions valid");
}

#[test]
fn test_soundness_empty_trail_valid() {
    verify_decision_soundness(&CdclState::new(2, vec![vec![1, -2]]))
        .expect("empty trail trivially sound");
}

// ---- Activity monotonicity ----

#[test]
fn test_activity_monotone_single_conflict() {
    let mut sc = VsidsScores::new(5, 0.95);
    sc.bump(1);
    sc.bump(2);
    assert!(verify_activity_monotone(&sc, &[vec![1, 2]]));
}

#[test]
fn test_activity_monotone_repeated_bumps() {
    let mut sc = VsidsScores::new(5, 0.95);
    sc.bump(1);
    sc.decay();
    sc.bump(1);
    sc.bump(3);
    assert!(verify_activity_monotone(&sc, &[vec![1], vec![1, 3]]));
}

#[test]
fn test_activity_monotone_empty_conflicts() {
    assert!(verify_activity_monotone(&VsidsScores::new(3, 0.95), &[]));
}

#[test]
fn test_activity_monotone_disjoint_vars() {
    let mut sc = VsidsScores::new(5, 0.95);
    sc.bump(1);
    sc.decay();
    sc.bump(2);
    assert!(verify_activity_monotone(&sc, &[vec![1], vec![2]]));
}

#[test]
fn test_activity_monotone_out_of_range_var_ignored() {
    assert!(verify_activity_monotone(
        &VsidsScores::new(3, 0.95),
        &[vec![0, 100]]
    ));
}

// ---- Decay bounded ----

#[test]
fn test_decay_bounded_fresh_scores() {
    assert!(verify_decay_bounded(&VsidsScores::new(5, 0.95), 1e100));
}

#[test]
fn test_decay_bounded_after_bumps() {
    let mut sc = VsidsScores::new(3, 0.95);
    for _ in 0..100 {
        sc.bump(1);
        sc.decay();
    }
    assert!(verify_decay_bounded(&sc, 1e100));
}

#[test]
fn test_decay_bounded_zero_bound_fails() {
    let mut sc = VsidsScores::new(3, 0.95);
    sc.bump(1);
    assert!(!verify_decay_bounded(&sc, 0.0));
}

#[test]
fn test_decay_bounded_exact_bound() {
    let mut sc = VsidsScores::new(3, 0.95);
    sc.bump(1);
    assert!(verify_decay_bounded(&sc, sc.activity(1)));
}

#[test]
fn test_decay_bounded_many_decays_still_finite() {
    let mut sc = VsidsScores::new(3, 0.95);
    for _ in 0..5000 {
        sc.decay();
        sc.bump(1);
    }
    assert!(verify_decay_bounded(&sc, 1e101));
}

// ---- Phase saving consistency ----

#[test]
fn test_phase_saving_consistent_basic() {
    let mut s = CdclState::new(3, vec![vec![1, -2, 3]]);
    s.decide(1).unwrap();
    s.assign(-2, Some(0)).unwrap();
    assert!(verify_phase_saving_consistent(
        &s,
        &[None, Some(true), Some(false), None]
    ));
}

#[test]
fn test_phase_saving_wrong_polarity_fails() {
    let mut s = CdclState::new(2, vec![vec![1, -2]]);
    s.decide(1).unwrap();
    assert!(!verify_phase_saving_consistent(&s, &[None, Some(false)]));
}

#[test]
fn test_phase_saving_unassigned_var_with_saved_phase_fails() {
    assert!(!verify_phase_saving_consistent(
        &CdclState::new(2, vec![vec![1, -2]]),
        &[None, Some(true), None]
    ));
}

#[test]
fn test_phase_saving_all_none_passes() {
    let mut s = CdclState::new(3, vec![vec![1, 2, 3]]);
    s.decide(1).unwrap();
    assert!(verify_phase_saving_consistent(
        &s,
        &[None, None, None, None]
    ));
}

#[test]
fn test_phase_saving_empty_state() {
    assert!(verify_phase_saving_consistent(
        &CdclState::new(0, vec![]),
        &[]
    ));
}

// ---- Decision rate ----

#[test]
fn test_decision_rate_all_decisions() {
    let trail = [
        TrailEntry {
            literal: 1,
            decision_level: 1,
            reason: None,
        },
        TrailEntry {
            literal: 2,
            decision_level: 2,
            reason: None,
        },
        TrailEntry {
            literal: 3,
            decision_level: 3,
            reason: None,
        },
    ];
    let (d, p, rate) = compute_decision_rate(&trail);
    assert_eq!((d, p), (3, 0));
    assert!((rate - 1.0).abs() < 1e-15);
}

#[test]
fn test_decision_rate_all_propagations() {
    let trail = [
        TrailEntry {
            literal: 1,
            decision_level: 0,
            reason: Some(0),
        },
        TrailEntry {
            literal: 2,
            decision_level: 0,
            reason: Some(1),
        },
    ];
    let (d, p, rate) = compute_decision_rate(&trail);
    assert_eq!((d, p), (0, 2));
    assert!(rate.abs() < 1e-15);
}

#[test]
fn test_decision_rate_mixed() {
    let trail = [
        TrailEntry {
            literal: 1,
            decision_level: 1,
            reason: None,
        },
        TrailEntry {
            literal: 2,
            decision_level: 1,
            reason: Some(0),
        },
        TrailEntry {
            literal: 3,
            decision_level: 1,
            reason: Some(1),
        },
        TrailEntry {
            literal: 4,
            decision_level: 2,
            reason: None,
        },
    ];
    let (d, p, rate) = compute_decision_rate(&trail);
    assert_eq!((d, p), (2, 2));
    assert!((rate - 0.5).abs() < 1e-15);
}

#[test]
fn test_decision_rate_empty_trail() {
    let (d, p, rate) = compute_decision_rate(&[]);
    assert_eq!((d, p), (0, 0));
    assert!(rate.abs() < 1e-15);
}

// ---- Branching completeness ----

#[test]
fn test_branching_complete_picks_unassigned() {
    let mut sc = VsidsScores::new(3, 0.95);
    sc.bump(2);
    assert!(verify_branching_complete(&sc, &[None; 4]));
}

#[test]
fn test_branching_complete_all_assigned_returns_none() {
    let sc = VsidsScores::new(2, 0.95);
    assert!(verify_branching_complete(
        &sc,
        &[None, Some(AssignValue::True), Some(AssignValue::False)]
    ));
}

#[test]
fn test_branching_complete_partial_assignment() {
    let mut sc = VsidsScores::new(3, 0.95);
    sc.bump(3);
    assert!(verify_branching_complete(
        &sc,
        &[None, Some(AssignValue::True), None, None]
    ));
}

#[test]
fn test_branching_complete_single_var() {
    assert!(verify_branching_complete(
        &VsidsScores::new(1, 0.95),
        &[None, None]
    ));
}

// ---- Heuristic comparison ----

#[test]
fn test_compare_heuristics_identical_traces() {
    let trace = [
        TrailEntry {
            literal: 1,
            decision_level: 1,
            reason: None,
        },
        TrailEntry {
            literal: 2,
            decision_level: 1,
            reason: Some(0),
        },
    ];
    let cmp = compare_heuristics(&trace, &trace, 1, 1);
    assert_eq!(cmp.decisions_a, cmp.decisions_b);
    assert_eq!(cmp.propagations_a, cmp.propagations_b);
}

#[test]
fn test_compare_heuristics_different_decision_counts() {
    let a = [
        TrailEntry {
            literal: 1,
            decision_level: 1,
            reason: None,
        },
        TrailEntry {
            literal: 2,
            decision_level: 1,
            reason: Some(0),
        },
        TrailEntry {
            literal: 3,
            decision_level: 2,
            reason: None,
        },
    ];
    let b = [
        TrailEntry {
            literal: 2,
            decision_level: 1,
            reason: None,
        },
        TrailEntry {
            literal: 1,
            decision_level: 1,
            reason: Some(0),
        },
        TrailEntry {
            literal: 3,
            decision_level: 1,
            reason: Some(1),
        },
    ];
    let cmp = compare_heuristics(&a, &b, 2, 0);
    assert_eq!((cmp.decisions_a, cmp.decisions_b), (2, 1));
    assert_eq!((cmp.propagations_a, cmp.propagations_b), (1, 2));
    assert_eq!((cmp.conflicts_a, cmp.conflicts_b), (2, 0));
}

#[test]
fn test_compare_heuristics_empty_traces() {
    let cmp = compare_heuristics(&[], &[], 0, 0);
    assert_eq!(
        cmp,
        HeuristicComparison {
            decisions_a: 0,
            decisions_b: 0,
            conflicts_a: 0,
            conflicts_b: 0,
            propagations_a: 0,
            propagations_b: 0,
        }
    );
}

// ---- Restart preserves heuristic ----

#[test]
fn test_restart_preserves_heuristic_identical() {
    let mut sc = VsidsScores::new(5, 0.95);
    sc.bump(1);
    sc.bump(3);
    sc.decay();
    assert!(verify_restart_preserves_heuristic(&sc, &sc.clone()));
}

#[test]
fn test_restart_preserves_heuristic_different_bumps_fail() {
    let mut before = VsidsScores::new(3, 0.95);
    before.bump(1);
    let mut after = before.clone();
    after.bump(2);
    assert!(!verify_restart_preserves_heuristic(&before, &after));
}

#[test]
fn test_restart_preserves_heuristic_different_sizes_fail() {
    assert!(!verify_restart_preserves_heuristic(
        &VsidsScores::new(3, 0.95),
        &VsidsScores::new(5, 0.95),
    ));
}

#[test]
fn test_restart_preserves_heuristic_fresh_scores() {
    assert!(verify_restart_preserves_heuristic(
        &VsidsScores::new(10, 0.95),
        &VsidsScores::new(10, 0.80),
    ));
}

// ---- Satisfying trace ----

#[test]
fn test_satisfying_trace_simple_sat() {
    let mut s = CdclState::new(2, vec![vec![1, 2], vec![-1, 2]]);
    s.decide(2).unwrap();
    s.assign(1, Some(0)).unwrap();
    verify_satisfying_trace(&s).expect("satisfying assignment");
}

#[test]
fn test_satisfying_trace_incomplete_fails() {
    let mut s = CdclState::new(3, vec![vec![1, 2, 3]]);
    s.decide(1).unwrap();
    assert!(verify_satisfying_trace(&s).is_err());
}

#[test]
fn test_satisfying_trace_unsatisfied_clause_fails() {
    let mut s = CdclState::new(2, vec![vec![1], vec![-1]]);
    s.decide(1).unwrap();
    s.assign(-2, None).unwrap();
    assert!(verify_satisfying_trace(&s).is_err());
}

// ---- Valid ordering ----

#[test]
fn test_valid_ordering_correct() {
    assert!(verify_valid_ordering(&[1, 2, 3], 3));
    assert!(verify_valid_ordering(&[3, 1, 2], 3));
}

#[test]
fn test_valid_ordering_single_var() {
    assert!(verify_valid_ordering(&[1], 1));
}

#[test]
fn test_valid_ordering_empty() {
    assert!(verify_valid_ordering(&[], 0));
}

#[test]
fn test_valid_ordering_duplicate_fails() {
    assert!(!verify_valid_ordering(&[1, 1, 2], 3));
}

#[test]
fn test_valid_ordering_zero_var_fails() {
    assert!(!verify_valid_ordering(&[0, 1, 2], 3));
}

#[test]
fn test_valid_ordering_out_of_range_fails() {
    assert!(!verify_valid_ordering(&[1, 2, 4], 3));
}

#[test]
fn test_valid_ordering_wrong_length_fails() {
    assert!(!verify_valid_ordering(&[1, 2], 3));
}

// ---- HeuristicProperty enum ----

#[test]
fn test_heuristic_property_variants() {
    assert_ne!(
        HeuristicProperty::Completeness,
        HeuristicProperty::Soundness
    );
    assert_ne!(
        HeuristicProperty::Soundness,
        HeuristicProperty::FairnessLowerBound
    );
    assert_ne!(
        HeuristicProperty::Completeness,
        HeuristicProperty::FairnessLowerBound
    );
}

#[test]
fn test_heuristic_property_debug() {
    assert!(format!("{:?}", HeuristicProperty::Soundness).contains("Soundness"));
}

// ---- Proof status constants ----

#[test]
fn test_proof_status_constants() {
    assert_eq!(S07A_DECISION_COMPLETENESS, ProofStatus::DerivedPending);
    assert_eq!(S07B_DECISION_SOUNDNESS, ProofStatus::DerivedPending);
    assert_eq!(S07C_ACTIVITY_BOUNDED, ProofStatus::DerivedPending);
}

// ---- Integration tests ----

#[test]
fn test_integration_decision_then_propagation() {
    let mut s = CdclState::new(3, vec![vec![1, 2], vec![-1, 3], vec![-2, 3]]);
    s.decide(3).unwrap();
    s.decide(1).unwrap();
    s.assign(2, Some(0)).unwrap();
    verify_decision_completeness(&s).expect("all vars covered");
    verify_decision_soundness(&s).expect("valid trace");
    let (d, p, rate) = compute_decision_rate(&s.trail);
    assert_eq!((d, p), (2, 1));
    assert!((rate - 2.0 / 3.0).abs() < 1e-10);
}

#[test]
fn test_integration_all_propagation_no_decisions_needed() {
    let mut s = CdclState::new(2, vec![vec![1], vec![2]]);
    s.assign(1, Some(0)).unwrap();
    s.assign(2, Some(1)).unwrap();
    verify_decision_completeness(&s).expect("all vars on trail");
    let (d, _, rate) = compute_decision_rate(&s.trail);
    assert_eq!(d, 0);
    assert!(rate.abs() < 1e-15);
}

#[test]
fn test_integration_restart_cycle() {
    let mut sc = VsidsScores::new(4, 0.95);
    sc.bump(1);
    sc.bump(2);
    sc.bump(2);
    sc.decay();
    let saved = sc.clone();
    let mut s = CdclState::new(4, vec![vec![1, -2, 3, 4]]);
    s.decide(2).unwrap();
    s.decide(1).unwrap();
    s.backtrack_to(0).unwrap();
    assert!(verify_restart_preserves_heuristic(&saved, &sc));
    assert!(verify_branching_complete(&sc, &s.assignment));
}

#[test]
fn test_integration_same_formula_different_orderings() {
    let clauses = vec![vec![1, 2], vec![-1, 2]];
    let mut sa = CdclState::new(2, clauses.clone());
    sa.decide(1).unwrap();
    sa.assign(2, Some(0)).unwrap();
    let mut sb = CdclState::new(2, clauses);
    sb.decide(2).unwrap();
    sb.assign(1, Some(0)).unwrap();
    verify_satisfying_trace(&sa).expect("ordering A satisfies");
    verify_satisfying_trace(&sb).expect("ordering B satisfies");
}

#[test]
fn test_integration_unsatisfiable_formula() {
    let mut s = CdclState::new(1, vec![vec![1], vec![-1]]);
    s.decide(1).unwrap();
    assert!(verify_satisfying_trace(&s).is_err());
}
