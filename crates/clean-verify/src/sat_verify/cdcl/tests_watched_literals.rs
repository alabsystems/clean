// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for watched literal propagation correctness (S02a/b/c).

#[cfg(test)]
mod tests {
    use crate::sat_verify::cdcl::watched_literals::{
        build_watch_lists, clause_is_satisfied, count_active_watches, propagate_watch,
        verify_watch_after_assignment, verify_watch_completeness, verify_watch_invariant,
        verify_watch_symmetry, WatchList, WatchPropagateResult, S02A_WATCH_INVARIANT,
        S02B_WATCH_PROPAGATION_SOUND, S02C_WATCH_COMPLETENESS,
    };
    use crate::sat_verify::cdcl::{negate, var_of, CdclState};
    use crate::spec::ProofStatus;

    #[test]
    fn test_proof_status_constants() {
        assert_eq!(S02A_WATCH_INVARIANT, ProofStatus::DerivedPending);
        assert_eq!(S02B_WATCH_PROPAGATION_SOUND, ProofStatus::DerivedPending);
        assert_eq!(S02C_WATCH_COMPLETENESS, ProofStatus::DerivedPending);
    }

    #[test]
    fn test_build_watch_lists_empty_formula() {
        let state = CdclState::new(3, vec![]);
        let wl = build_watch_lists(&state);
        assert_eq!(wl.total_watches(), 0);
    }

    #[test]
    fn test_build_watch_lists_single_binary_clause() {
        let state = CdclState::new(2, vec![vec![1, -2]]);
        let wl = build_watch_lists(&state);
        assert!(wl.watchers_of(1).contains(&0));
        assert!(wl.watchers_of(-2).contains(&0));
        assert_eq!(wl.total_watches(), 2);
    }

    #[test]
    fn test_build_watch_lists_unit_clause() {
        let state = CdclState::new(1, vec![vec![1]]);
        let wl = build_watch_lists(&state);
        assert!(wl.watchers_of(1).contains(&0));
        assert_eq!(wl.total_watches(), 1);
    }

    #[test]
    fn test_build_watch_lists_multiple_clauses() {
        let state = CdclState::new(3, vec![vec![1, -2, 3], vec![-1, 2], vec![2, 3]]);
        let wl = build_watch_lists(&state);
        assert!(wl.watchers_of(1).contains(&0));
        assert!(wl.watchers_of(-2).contains(&0));
        assert!(wl.watchers_of(-1).contains(&1));
        assert!(wl.watchers_of(2).contains(&1));
        assert!(wl.watchers_of(2).contains(&2));
        assert!(wl.watchers_of(3).contains(&2));
        assert_eq!(wl.total_watches(), 6);
    }

    #[test]
    fn test_build_watch_lists_empty_clause_skipped() {
        let mut state = CdclState::new(2, vec![vec![1, 2]]);
        state.clauses.push(vec![]);
        state.watches.push((0, 0));
        let wl = build_watch_lists(&state);
        assert_eq!(wl.total_watches(), 2);
    }

    #[test]
    fn test_watchers_of_absent_literal_is_empty() {
        let state = CdclState::new(3, vec![vec![1, 2]]);
        let wl = build_watch_lists(&state);
        assert!(wl.watchers_of(3).is_empty());
        assert!(wl.watchers_of(-3).is_empty());
    }

    #[test]
    fn test_watch_invariant_fresh_state_holds() {
        let state = CdclState::new(3, vec![vec![1, -2, 3], vec![-1, 2]]);
        verify_watch_invariant(&state).expect("fresh state should satisfy invariant");
    }

    #[test]
    fn test_watch_invariant_after_one_assignment_holds() {
        let mut state = CdclState::new(3, vec![vec![1, -2, 3], vec![-1, 2]]);
        state.assign(-1, None).expect("assign");
        verify_watch_invariant(&state).expect("invariant should hold");
    }

    #[test]
    fn test_watch_invariant_satisfied_clause_not_checked() {
        let mut state = CdclState::new(2, vec![vec![1, 2]]);
        state.assign(1, None).expect("assign");
        verify_watch_invariant(&state).expect("satisfied clause is exempt");
    }

    #[test]
    fn test_watch_invariant_violation_both_false() {
        let mut state = CdclState::new(3, vec![vec![1, 2, 3]]);
        state.assign(-1, None).expect("assign");
        state.assign(-2, None).expect("assign");
        assert!(
            verify_watch_invariant(&state).is_err(),
            "both watches false"
        );
    }

    #[test]
    fn test_watch_invariant_one_true_one_false_ok() {
        let mut state = CdclState::new(2, vec![vec![1, 2]]);
        state.assign(1, None).expect("assign");
        state.assign(-2, None).expect("assign");
        verify_watch_invariant(&state).expect("one true watch suffices");
    }

    #[test]
    fn test_watch_invariant_unit_clause_skipped() {
        let mut state = CdclState::new(2, vec![vec![1]]);
        state.assign(-1, None).expect("assign");
        verify_watch_invariant(&state).expect("unit clause not checked");
    }

    #[test]
    fn test_watch_completeness_fresh_state() {
        let state = CdclState::new(3, vec![vec![1, -2, 3], vec![-1, 2]]);
        verify_watch_completeness(&state).expect("fresh state complete");
    }

    #[test]
    fn test_watch_completeness_both_false_but_satisfied_elsewhere() {
        let mut state = CdclState::new(3, vec![vec![1, 2, 3]]);
        state.assign(-1, None).expect("a");
        state.assign(-2, None).expect("a");
        state.assign(3, None).expect("a");
        verify_watch_completeness(&state).expect("clause satisfied elsewhere");
    }

    #[test]
    fn test_watch_completeness_violation_both_false_not_satisfied() {
        let mut state = CdclState::new(3, vec![vec![1, 2, 3]]);
        state.assign(-1, None).expect("a");
        state.assign(-2, None).expect("a");
        assert!(
            verify_watch_completeness(&state).is_err(),
            "both false, not satisfied"
        );
    }

    #[test]
    fn test_watch_completeness_all_false_violation() {
        let mut state = CdclState::new(3, vec![vec![1, 2, 3]]);
        state.assign(-1, None).expect("a");
        state.assign(-2, None).expect("a");
        state.assign(-3, None).expect("a");
        assert!(verify_watch_completeness(&state).is_err(), "all false");
    }

    #[test]
    fn test_propagate_finds_new_watch_in_long_clause() {
        let mut state = CdclState::new(4, vec![vec![1, 2, 3, 4]]);
        state.assign(-1, None).expect("a");
        match propagate_watch(&state, 0, 1) {
            WatchPropagateResult::NewWatch {
                clause_idx,
                new_watch_pos,
            } => {
                assert_eq!(clause_idx, 0);
                assert!(new_watch_pos == 2 || new_watch_pos == 3);
            }
            other => panic!("expected NewWatch, got {other:?}"),
        }
    }

    #[test]
    fn test_propagate_detects_unit_clause() {
        let mut state = CdclState::new(2, vec![vec![1, 2]]);
        state.assign(-1, None).expect("a");
        match propagate_watch(&state, 0, 1) {
            WatchPropagateResult::Unit {
                clause_idx,
                implied_lit,
            } => {
                assert_eq!(clause_idx, 0);
                assert_eq!(implied_lit, 2);
            }
            other => panic!("expected Unit, got {other:?}"),
        }
    }

    #[test]
    fn test_propagate_detects_conflict() {
        let mut state = CdclState::new(2, vec![vec![1, 2]]);
        state.assign(-1, None).expect("a");
        state.assign(-2, None).expect("a");
        match propagate_watch(&state, 0, 1) {
            WatchPropagateResult::Conflict { clause_idx } => assert_eq!(clause_idx, 0),
            other => panic!("expected Conflict, got {other:?}"),
        }
    }

    #[test]
    fn test_propagate_other_watch_true_keeps_current() {
        let mut state = CdclState::new(3, vec![vec![1, 2, 3]]);
        state.assign(2, None).expect("a");
        state.assign(-1, None).expect("a");
        match propagate_watch(&state, 0, 1) {
            WatchPropagateResult::NewWatch { clause_idx, .. } => assert_eq!(clause_idx, 0),
            other => panic!("expected NewWatch (satisfied), got {other:?}"),
        }
    }

    #[test]
    fn test_propagate_second_watch_false() {
        let mut state = CdclState::new(3, vec![vec![1, 2, 3]]);
        state.assign(-2, None).expect("a");
        match propagate_watch(&state, 0, 2) {
            WatchPropagateResult::NewWatch { new_watch_pos, .. } => {
                assert_eq!(new_watch_pos, 2, "should find literal 3 at pos 2");
            }
            other => panic!("expected NewWatch, got {other:?}"),
        }
    }

    #[test]
    fn test_propagate_skips_false_non_watched_literals() {
        let mut state = CdclState::new(4, vec![vec![1, 2, 3, 4]]);
        state.assign(-3, None).expect("a");
        state.assign(-4, None).expect("a");
        state.assign(-1, None).expect("a");
        match propagate_watch(&state, 0, 1) {
            WatchPropagateResult::Unit { implied_lit, .. } => assert_eq!(implied_lit, 2),
            other => panic!("expected Unit, got {other:?}"),
        }
    }

    #[test]
    fn test_propagate_finds_true_non_watched_literal() {
        let mut state = CdclState::new(4, vec![vec![1, 2, 3, 4]]);
        state.assign(3, None).expect("a");
        state.assign(-1, None).expect("a");
        match propagate_watch(&state, 0, 1) {
            WatchPropagateResult::NewWatch { new_watch_pos, .. } => {
                assert_eq!(new_watch_pos, 2, "should pick true literal at pos 2");
            }
            other => panic!("expected NewWatch, got {other:?}"),
        }
    }

    #[test]
    fn test_watch_symmetry_fresh_state() {
        let state = CdclState::new(3, vec![vec![1, -2, 3], vec![-1, 2]]);
        verify_watch_symmetry(&state).expect("fresh state symmetric");
    }

    #[test]
    fn test_watch_symmetry_unit_clause_ok() {
        let state = CdclState::new(1, vec![vec![1]]);
        verify_watch_symmetry(&state).expect("unit clause w0==w1 is OK");
    }

    #[test]
    fn test_watch_symmetry_violation_same_index() {
        let mut state = CdclState::new(3, vec![vec![1, 2, 3]]);
        state.watches[0] = (0, 0);
        assert!(
            verify_watch_symmetry(&state).is_err(),
            "same index violation"
        );
    }

    #[test]
    fn test_watch_symmetry_violation_out_of_bounds() {
        let mut state = CdclState::new(2, vec![vec![1, 2]]);
        state.watches[0] = (0, 5);
        assert!(
            verify_watch_symmetry(&state).is_err(),
            "out of bounds violation"
        );
    }

    #[test]
    fn test_watch_symmetry_duplicate_literals_violation() {
        let mut state = CdclState::new(2, vec![vec![1, 1, 2]]);
        state.watches[0] = (0, 1);
        assert!(
            verify_watch_symmetry(&state).is_err(),
            "same literal violation"
        );
    }

    #[test]
    fn test_watch_after_assignment_holds_when_other_watch_unassigned() {
        let mut state = CdclState::new(3, vec![vec![1, 2, 3]]);
        state.assign(1, None).expect("a");
        verify_watch_after_assignment(&state, 1).expect("other watch unassigned");
    }

    #[test]
    fn test_watch_after_assignment_violation() {
        let mut state = CdclState::new(3, vec![vec![1, 2, 3]]);
        state.assign(-1, None).expect("a");
        state.assign(-2, None).expect("a");
        // Checking clauses watching negate(-1)=1: clause 0 watches lit 1.
        assert!(
            verify_watch_after_assignment(&state, -1).is_err(),
            "both false"
        );
    }

    #[test]
    fn test_watch_after_assignment_skips_non_watching_clauses() {
        let mut state = CdclState::new(3, vec![vec![1, 2], vec![2, 3]]);
        state.assign(-1, None).expect("a");
        // Clause 1 does not watch literal 1, so it's skipped.
        verify_watch_after_assignment(&state, -1).expect("clause 1 not affected");
    }

    #[test]
    fn test_count_active_watches_empty() {
        let state = CdclState::new(2, vec![]);
        let counts = count_active_watches(&state);
        assert!(counts.iter().all(|&c| c == 0));
    }

    #[test]
    fn test_count_active_watches_two_clauses_sharing_literal() {
        let state = CdclState::new(3, vec![vec![1, 2], vec![1, 3]]);
        let wl = WatchList::build(&state);
        assert_eq!(wl.watchers_of(1).len(), 2, "literal 1 watched by 2 clauses");
        assert_eq!(wl.watchers_of(2).len(), 1);
        assert_eq!(wl.watchers_of(3).len(), 1);
    }

    #[test]
    fn test_clause_is_satisfied_unassigned() {
        let state = CdclState::new(2, vec![]);
        assert!(!clause_is_satisfied(&state, &[1, 2]));
    }

    #[test]
    fn test_clause_is_satisfied_true() {
        let mut state = CdclState::new(2, vec![]);
        state.assign(1, None).expect("a");
        assert!(clause_is_satisfied(&state, &[1, 2]));
    }

    #[test]
    fn test_clause_is_satisfied_all_false() {
        let mut state = CdclState::new(2, vec![]);
        state.assign(-1, None).expect("a");
        state.assign(-2, None).expect("a");
        assert!(!clause_is_satisfied(&state, &[1, 2]));
    }

    #[test]
    fn test_tautological_clause_invariant_holds() {
        let state = CdclState::new(1, vec![vec![1, -1]]);
        verify_watch_invariant(&state).expect("tautology always satisfies invariant");
    }

    #[test]
    fn test_tautological_clause_assigned_still_ok() {
        let mut state = CdclState::new(1, vec![vec![1, -1]]);
        state.assign(1, None).expect("a");
        verify_watch_invariant(&state).expect("tautology satisfied after assign");
    }

    #[test]
    fn test_backtrack_restores_watch_invariant() {
        let mut state = CdclState::new(3, vec![vec![1, 2, 3]]);
        state.decide(-1).expect("d");
        state.decide(-2).expect("d");
        assert!(
            verify_watch_invariant(&state).is_err(),
            "both watches false"
        );
        state.backtrack_to(0).expect("bt");
        verify_watch_invariant(&state).expect("after backtrack, invariant restored");
    }

    #[test]
    fn test_backtrack_partial_restores_invariant() {
        let mut state = CdclState::new(3, vec![vec![1, 2, 3]]);
        state.decide(-1).expect("d");
        state.decide(-2).expect("d");
        state.backtrack_to(1).expect("bt");
        verify_watch_invariant(&state).expect("partial backtrack restores invariant");
    }

    #[test]
    fn test_learned_clause_watch_invariant() {
        let mut state = CdclState::new(3, vec![vec![1, 2]]);
        state.add_learned_clause(vec![-1, 3]);
        verify_watch_invariant(&state).expect("learned clause satisfies invariant");
        verify_watch_symmetry(&state).expect("learned clause has symmetric watches");
    }

    #[test]
    fn test_propagate_ternary_clause_all_non_watched_false() {
        let mut state = CdclState::new(3, vec![vec![1, 2, 3]]);
        state.assign(-3, None).expect("a");
        state.assign(-1, None).expect("a");
        match propagate_watch(&state, 0, 1) {
            WatchPropagateResult::Unit { implied_lit, .. } => assert_eq!(implied_lit, 2),
            other => panic!("expected Unit, got {other:?}"),
        }
    }

    #[test]
    fn test_var_of_negate_helpers() {
        assert_eq!(var_of(5), 5);
        assert_eq!(var_of(-3), 3);
        assert_eq!(negate(5), -5);
        assert_eq!(negate(-3), 3);
    }

    #[test]
    fn test_large_formula_watch_invariant() {
        let state = CdclState::new(
            5,
            vec![vec![1, -2, 3], vec![-1, 4, -5], vec![2, 5], vec![-3, -4, 1]],
        );
        verify_watch_invariant(&state).expect("large formula fresh");
        verify_watch_symmetry(&state).expect("large formula symmetric");
        verify_watch_completeness(&state).expect("large formula complete");
    }

    #[test]
    fn test_watch_list_method_equivalence() {
        let state = CdclState::new(3, vec![vec![1, 2], vec![2, 3], vec![-1, -3]]);
        let wl1 = build_watch_lists(&state);
        let wl2 = WatchList::build(&state);
        assert_eq!(wl1.total_watches(), wl2.total_watches());
    }
}
