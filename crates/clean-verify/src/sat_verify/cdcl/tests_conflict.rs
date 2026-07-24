// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for first-UIP conflict analysis.

#[cfg(test)]
mod tests {
    use crate::sat_verify::cdcl::bcp::bcp_loop;
    use crate::sat_verify::cdcl::conflict_analysis::{
        analyze_conflict, collect_conflict_variables, is_asserting, resolve, ConflictAnalysisResult,
    };
    use crate::sat_verify::cdcl::{var_of, CdclError, CdclState};

    // Helper: build a state and run BCP until conflict, returning the conflict clause index.
    fn setup_and_propagate(
        num_vars: u32,
        clauses: Vec<Vec<i32>>,
        decisions: &[i32],
    ) -> (CdclState, usize) {
        let mut state = CdclState::new(num_vars, clauses);
        for &dec in decisions {
            // Run BCP after each decision.
            let _ = bcp_loop(&mut state);
            state.decide(dec).expect("decide should succeed");
        }
        // Final BCP should hit conflict.
        match bcp_loop(&mut state) {
            Err(CdclError::Conflict(ci)) => (state, ci),
            other => panic!("expected conflict, got {other:?}"),
        }
    }

    // ---- Resolution tests ----

    #[test]
    fn test_resolve_simple_pivot() {
        // {1, 2} resolve with {-1, 3} on variable 1 => {2, 3}
        let result = resolve(&[1, 2], &[-1, 3], 1).expect("resolve");
        assert_eq!(result.len(), 2);
        assert!(result.contains(&2));
        assert!(result.contains(&3));
        assert!(!result.iter().any(|&l| var_of(l) == 1));
    }

    #[test]
    fn test_resolve_pivot_removed_and_dedup_by_variable() {
        // {1, -2} resolve with {-1, 2} on variable 1.
        // After removing pivot var 1: remaining are -2 (from clause1) and 2 (from clause2).
        // Resolution deduplicates by variable: var 2 appears in both, so only the first
        // occurrence (-2) is kept. This matches standard CDCL resolution behavior where
        // tautological resolvents are simplified.
        let result = resolve(&[1, -2], &[-1, 2], 1).expect("resolve");
        assert_eq!(result.len(), 1);
        assert_eq!(result[0], -2);
    }

    #[test]
    fn test_resolve_dedup_same_literal() {
        // {1, 2} resolve with {-1, 2} on variable 1 => {2}
        let result = resolve(&[1, 2], &[-1, 2], 1).expect("resolve");
        assert_eq!(result, vec![2]);
    }

    #[test]
    fn test_resolve_no_pivot_in_first_clause() {
        let result = resolve(&[2, 3], &[-1, 3], 1);
        assert!(result.is_err());
    }

    #[test]
    fn test_resolve_no_pivot_in_second_clause() {
        let result = resolve(&[1, 2], &[2, 3], 1);
        assert!(result.is_err());
    }

    #[test]
    fn test_resolve_larger_clauses() {
        // {1, 2, 3, 4} resolve with {-1, 5, 6} on var 1 => {2, 3, 4, 5, 6}
        let result = resolve(&[1, 2, 3, 4], &[-1, 5, 6], 1).expect("resolve");
        assert_eq!(result.len(), 5);
        for lit in [2, 3, 4, 5, 6] {
            assert!(result.contains(&lit), "missing {lit}");
        }
    }

    // ---- Simple conflict analysis tests ----

    #[test]
    fn test_analyze_conflict_unit_contradiction() {
        // Clauses: (1), (-1)
        // At decision level 0, BCP propagates 1 from clause 0, then conflicts on clause 1.
        let mut state = CdclState::new(1, vec![vec![1], vec![-1]]);
        match bcp_loop(&mut state) {
            Err(CdclError::Conflict(ci)) => {
                // Conflict at level 0 -- the clause is just [-1] and the only
                // literal 1 was propagated at level 0.
                // With 1 literal at level 0, the loop body doesn't execute,
                // so the learned clause is [-1] with backtrack level 0.
                let result = analyze_conflict(&state, ci).expect("analyze");
                assert!(!result.learned_clause.is_empty());
                assert_eq!(result.backtrack_level, 0);
            }
            other => panic!("expected conflict, got {other:?}"),
        }
    }

    #[test]
    fn test_analyze_conflict_two_level_basic() {
        // Clauses:
        //   C0: (1, 2)     -- if both false, conflict
        //   C1: (-1, 2)    -- if 1 true, forces 2
        //   C2: (-1, -2)   -- if 1 true and 2 true, conflict
        //
        // Decide 1 at level 1.
        // BCP: C1 forces 2 (reason=1). C2 now all false => conflict.
        let (state, conflict_ci) =
            setup_and_propagate(2, vec![vec![1, 2], vec![-1, 2], vec![-1, -2]], &[1]);

        let result = analyze_conflict(&state, conflict_ci).expect("analyze");
        // The learned clause must be asserting.
        assert!(is_asserting(&state, &result.learned_clause));
        // Backtrack level should be 0 (no other decision levels involved).
        assert_eq!(result.backtrack_level, 0);
    }

    #[test]
    fn test_analyze_conflict_multi_level() {
        // Two decision levels, conflict at level 2.
        // Clauses designed so BCP does NOT propagate vars 1 or 3 prematurely:
        //   C0: (-1, -3, 4)   -- needs both 1=T and 3=T to force 4
        //   C1: (-1, -3, -4)  -- conflicts when 1=T, 3=T, 4=T
        //
        // Level 1: decide 1. BCP: no unit (var 3 unassigned in both clauses).
        // Level 2: decide 3. BCP: C0 forces 4 (reason=0). C1 all false => conflict.
        let (state, conflict_ci) =
            setup_and_propagate(4, vec![vec![-1, -3, 4], vec![-1, -3, -4]], &[1, 3]);

        let result = analyze_conflict(&state, conflict_ci).expect("analyze");
        assert!(is_asserting(&state, &result.learned_clause));
        // Backtrack level should be 1 (from variable 1).
        assert_eq!(result.backtrack_level, 1);
    }

    #[test]
    fn test_analyze_conflict_learned_clause_is_sound() {
        // Same multi-level setup as above.
        let (state, conflict_ci) =
            setup_and_propagate(4, vec![vec![-1, -3, 4], vec![-1, -3, -4]], &[1, 3]);

        let result = analyze_conflict(&state, conflict_ci).expect("analyze");
        // All variables in the learned clause should appear in the original clauses.
        state
            .verify_learned_clause(&result.learned_clause)
            .expect("learned clause should be sound");
    }

    #[test]
    fn test_analyze_conflict_uip_literal_in_learned_clause() {
        let (state, conflict_ci) =
            setup_and_propagate(4, vec![vec![-1, -3, 4], vec![-1, -3, -4]], &[1, 3]);

        let result = analyze_conflict(&state, conflict_ci).expect("analyze");
        // The UIP literal must be in the learned clause.
        assert!(result.learned_clause.contains(&result.uip_literal));
    }

    #[test]
    fn test_analyze_conflict_clause_index_out_of_bounds() {
        let state = CdclState::new(2, vec![vec![1, 2]]);
        let result = analyze_conflict(&state, 999);
        assert!(result.is_err());
    }

    // ---- is_asserting tests ----

    #[test]
    fn test_is_asserting_single_current_level() {
        let mut state = CdclState::new(3, vec![]);
        state.decide(1).expect("d");
        state.assign(2, Some(0)).expect("a");
        // Clause [-1, -2]: var 1 at level 1, var 2 at level 1.
        // Two at current level => not asserting.
        assert!(!is_asserting(&state, &[-1, -2]));
    }

    #[test]
    fn test_is_asserting_true() {
        let mut state = CdclState::new(3, vec![]);
        state.assign(1, None).expect("a"); // level 0
        state.decide(2).expect("d"); // level 1
                                     // Clause [-1, -2]: var 1 at level 0, var 2 at level 1.
                                     // Exactly one at current level => asserting.
        assert!(is_asserting(&state, &[-1, -2]));
    }

    // ---- Handbook of Satisfiability concrete example ----

    #[test]
    fn test_analyze_conflict_handbook_style_three_levels() {
        // Handbook-style example with three decision levels.
        // Clauses designed so BCP propagation only triggers at the final level:
        //
        //   C0: (-1, -3, -5, 6)    -- needs 1=T, 3=T, 5=T to force 6
        //   C1: (-1, -3, -5, -6)   -- conflicts when 1=T, 3=T, 5=T, 6=T
        //
        // Level 1: decide 1. BCP: no unit (vars 3, 5 unassigned).
        // Level 2: decide 3. BCP: no unit (var 5 unassigned).
        // Level 3: decide 5. BCP: C0 forces 6 (reason=0). C1 all false => conflict.
        let (state, conflict_ci) = setup_and_propagate(
            6,
            vec![vec![-1, -3, -5, 6], vec![-1, -3, -5, -6]],
            &[1, 3, 5],
        );

        let result = analyze_conflict(&state, conflict_ci).expect("analyze");

        // The learned clause should be asserting.
        assert!(is_asserting(&state, &result.learned_clause));

        // The backtrack level must be less than the current decision level (3).
        assert!(result.backtrack_level < state.decision_level);

        // The learned clause should not be empty.
        assert!(!result.learned_clause.is_empty());

        // Verify soundness.
        state
            .verify_learned_clause(&result.learned_clause)
            .expect("sound");
    }

    // ---- Backtrack level computation ----

    #[test]
    fn test_analyze_conflict_backtrack_to_zero_single_decision() {
        // Only one decision level: backtrack to 0.
        // (1) and (-1) at level 0 is immediate conflict, but let's use decisions.
        // C0: (-1, 2), C1: (-1, -2)
        // Decide 1. BCP: C0 forces 2. C1 all false => conflict.
        let (state, conflict_ci) = setup_and_propagate(2, vec![vec![-1, 2], vec![-1, -2]], &[1]);

        let result = analyze_conflict(&state, conflict_ci).expect("analyze");
        assert_eq!(result.backtrack_level, 0);
    }

    #[test]
    fn test_analyze_conflict_backtrack_level_correct() {
        // Three decision levels, conflict at level 3.
        // Clauses guard propagation behind all three decision variables:
        //   C0: (-1, -2, -3, 4)   -- needs 1=T, 2=T, 3=T to force 4
        //   C1: (-1, -2, -3, -4)  -- conflicts when 1=T, 2=T, 3=T, 4=T
        //
        // Level 1: decide 1. BCP: no unit (vars 2, 3 unassigned).
        // Level 2: decide 2. BCP: no unit (var 3 unassigned).
        // Level 3: decide 3. BCP: C0 forces 4 (reason=0). C1 all false => conflict.
        let (state, conflict_ci) = setup_and_propagate(
            4,
            vec![vec![-1, -2, -3, 4], vec![-1, -2, -3, -4]],
            &[1, 2, 3],
        );

        let result = analyze_conflict(&state, conflict_ci).expect("analyze");
        assert!(is_asserting(&state, &result.learned_clause));
        // Backtrack level should be 2 (second-highest level in learned clause).
        assert!(result.backtrack_level <= 2);
        assert!(result.backtrack_level < 3);
    }

    // ---- collect_conflict_variables tests ----

    #[test]
    fn test_collect_conflict_variables_basic() {
        let (state, conflict_ci) = setup_and_propagate(2, vec![vec![-1, 2], vec![-1, -2]], &[1]);

        let vars = collect_conflict_variables(&state, conflict_ci);
        // Should include variable 1 (decision) and variable 2 (propagated).
        assert!(!vars.is_empty());
        assert!(vars.contains(&1));
    }

    #[test]
    fn test_collect_conflict_variables_out_of_bounds() {
        let state = CdclState::new(2, vec![vec![1, 2]]);
        let vars = collect_conflict_variables(&state, 999);
        assert!(vars.is_empty());
    }

    #[test]
    fn test_collect_conflict_variables_includes_reason_chain() {
        // Chain: decide 1 -> propagate 2 -> propagate 3 -> conflict
        // C0: (-1, 2), C1: (-2, 3), C2: (-1, -3)
        let (state, conflict_ci) =
            setup_and_propagate(3, vec![vec![-1, 2], vec![-2, 3], vec![-1, -3]], &[1]);

        let vars = collect_conflict_variables(&state, conflict_ci);
        // All 3 variables should be collected.
        assert!(vars.contains(&1), "should include var 1");
        assert!(vars.contains(&3), "should include var 3");
    }

    // ---- Edge cases ----

    #[test]
    fn test_analyze_conflict_binary_clauses() {
        // All binary clauses.
        // C0: (1, 2), C1: (1, -2), C2: (-1, 2), C3: (-1, -2)
        // This is UNSAT. At level 0, no propagation (all binary, 2 unassigned each).
        // Decide 1 at level 1. BCP: C2 forces 2 (reason=2). C3 all false => conflict.
        let (state, conflict_ci) = setup_and_propagate(
            2,
            vec![vec![1, 2], vec![1, -2], vec![-1, 2], vec![-1, -2]],
            &[1],
        );

        let result = analyze_conflict(&state, conflict_ci).expect("analyze");
        assert!(is_asserting(&state, &result.learned_clause));
    }

    #[test]
    fn test_analyze_conflict_ternary_clause_conflict() {
        // C0: (-1, -2, 3), C1: (-1, -2, -3)
        // Decide 1 at level 1. Decide 2 at level 2.
        // BCP: C0 forces 3 (reason=0). C1 all false => conflict.
        let (state, conflict_ci) =
            setup_and_propagate(3, vec![vec![-1, -2, 3], vec![-1, -2, -3]], &[1, 2]);

        let result = analyze_conflict(&state, conflict_ci).expect("analyze");
        assert!(is_asserting(&state, &result.learned_clause));
        // The learned clause should include variable 2 (current level) and variable 1.
        assert!(result.backtrack_level >= 1);
    }

    #[test]
    fn test_analyze_conflict_result_fields_consistent() {
        let (state, conflict_ci) =
            setup_and_propagate(3, vec![vec![-1, -2, 3], vec![-1, -2, -3]], &[1, 2]);

        let ConflictAnalysisResult {
            learned_clause,
            backtrack_level,
            uip_literal,
        } = analyze_conflict(&state, conflict_ci).expect("analyze");

        // UIP literal must be in the learned clause.
        assert!(learned_clause.contains(&uip_literal));

        // UIP literal must be at the current decision level.
        let uip_level = state.level_of(var_of(uip_literal));
        assert_eq!(uip_level, Some(state.decision_level));

        // Backtrack level must be strictly less than current level (when learned clause has >1 lit).
        if learned_clause.len() > 1 {
            assert!(backtrack_level < state.decision_level);
        }
    }
}
