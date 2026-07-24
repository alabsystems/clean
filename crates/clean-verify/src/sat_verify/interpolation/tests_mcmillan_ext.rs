// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended tests for tree interpolation, strengthening, weakening,
//! verification, model counting, and formula size.

#[cfg(test)]
mod tests {
    use crate::sat_verify::interpolation::mcmillan::{
        count_interpolant_models, interpolant_size, strengthen_interpolant, tree_interpolant,
        verify_interpolant_property, weaken_interpolant, InterpolantVerifyResult, NodeKind,
    };
    use crate::sat_verify::interpolation::PropFormula;
    use std::collections::HashMap;

    // --- Helpers ---

    fn eval(f: &PropFormula, asgn: &[(u32, bool)]) -> bool {
        let map: HashMap<u32, bool> = asgn.iter().copied().collect();
        f.evaluate(&map)
    }

    // --- tree_interpolant tests ---

    #[test]
    fn test_tree_interpolant_single_a_unit_clause() {
        // A = {(1)}, B = {(-1)}, shared = {1}
        // Resolve on var 1 → empty clause
        let dag = vec![
            (vec![1], NodeKind::Input(0)),
            (vec![-1], NodeKind::Input(1)),
            (
                vec![],
                NodeKind::Resolve {
                    left: 0,
                    right: 1,
                    pivot: 1,
                },
            ),
        ];
        let interp = tree_interpolant(&dag, &[0], &[1]);
        // A implies I: when x1=true (satisfies A), I should be true
        assert!(eval(&interp, &[(1, true)]));
        // I AND B unsat: when x1=false (satisfies B), I should be false
        assert!(!eval(&interp, &[(1, false)]));
    }

    #[test]
    fn test_tree_interpolant_two_a_clauses_a_only_pivot() {
        // A = {(1,2), (-1,2)}, B = {(-2)}, shared = {2}, A-only = {1}
        // Resolve A clauses on var 1 → (2), then resolve with B on var 2
        let dag = vec![
            (vec![1, 2], NodeKind::Input(0)),
            (vec![-1, 2], NodeKind::Input(1)),
            (vec![-2], NodeKind::Input(2)),
            (
                vec![2],
                NodeKind::Resolve {
                    left: 0,
                    right: 1,
                    pivot: 1,
                },
            ),
            (
                vec![],
                NodeKind::Resolve {
                    left: 3,
                    right: 2,
                    pivot: 2,
                },
            ),
        ];
        let interp = tree_interpolant(&dag, &[0, 1], &[2]);
        // Var 1 should not appear (A-only)
        assert!(!interp.variables().contains(&1));
    }

    #[test]
    fn test_tree_interpolant_b_only_pivot() {
        // A = {(1)}, B = {(-1, 2), (-1, -2)}, shared = {1}, B-only = {2}
        // Resolve B clauses on var 2, then resolve with A on var 1
        let dag = vec![
            (vec![1], NodeKind::Input(0)),
            (vec![-1, 2], NodeKind::Input(1)),
            (vec![-1, -2], NodeKind::Input(2)),
            (
                vec![-1],
                NodeKind::Resolve {
                    left: 1,
                    right: 2,
                    pivot: 2,
                },
            ),
            (
                vec![],
                NodeKind::Resolve {
                    left: 0,
                    right: 3,
                    pivot: 1,
                },
            ),
        ];
        let interp = tree_interpolant(&dag, &[0], &[1]);
        assert!(!interp.variables().contains(&2));
    }

    #[test]
    fn test_tree_interpolant_empty_dag() {
        let interp = tree_interpolant(&[], &[], &[]);
        assert_eq!(interp, PropFormula::True);
    }

    #[test]
    fn test_tree_interpolant_only_b_input() {
        let dag = vec![(vec![1, 2], NodeKind::Input(0))];
        let interp = tree_interpolant(&dag, &[], &[1, 2]);
        assert_eq!(interp, PropFormula::True);
    }

    #[test]
    fn test_tree_interpolant_shared_pivot_produces_pudlak_form() {
        // A = {(1,2)}, B = {(-2)}, shared = {1,2}
        // Resolve on shared var 2
        let dag = vec![
            (vec![1, 2], NodeKind::Input(0)),
            (vec![-2], NodeKind::Input(1)),
            (
                vec![1],
                NodeKind::Resolve {
                    left: 0,
                    right: 1,
                    pivot: 2,
                },
            ),
        ];
        let interp = tree_interpolant(&dag, &[0], &[1, 2]);
        // Interpolant should use shared vars only
        let vars = interp.variables();
        assert!(vars.is_subset(&[1, 2].iter().copied().collect()));
    }

    #[test]
    fn test_tree_interpolant_craig_properties_hold() {
        // A = {(1,2)}, B = {(-1), (-2)}, shared = {1,2}
        let dag = vec![
            (vec![1, 2], NodeKind::Input(0)),
            (vec![-1], NodeKind::Input(1)),
            (vec![-2], NodeKind::Input(2)),
            (
                vec![2],
                NodeKind::Resolve {
                    left: 0,
                    right: 1,
                    pivot: 1,
                },
            ),
            (
                vec![],
                NodeKind::Resolve {
                    left: 3,
                    right: 2,
                    pivot: 2,
                },
            ),
        ];
        let interp = tree_interpolant(&dag, &[0], &[1, 2]);
        let result = verify_interpolant_property(&interp, &[vec![1, 2]], &[vec![-1], vec![-2]], 2);
        assert!(result.valid, "Craig properties should hold: {result:?}");
    }

    // --- strengthen_interpolant tests ---

    #[test]
    fn test_strengthen_with_matching_unit() {
        // I = x1, A has unit clause (1) → strengthened = x1 AND x1 = x1
        let interp = PropFormula::Var(1);
        let strengthened = strengthen_interpolant(&interp, &[vec![1]]);
        // Under x1=true, both original and strengthened are true
        assert!(eval(&strengthened, &[(1, true)]));
        // Under x1=false, strengthened should be false (at least as strong)
        assert!(!eval(&strengthened, &[(1, false)]));
    }

    #[test]
    fn test_strengthen_no_matching_units() {
        let interp = PropFormula::Var(1);
        let strengthened = strengthen_interpolant(&interp, &[vec![2, 3]]);
        // No unit clauses with var 1 → unchanged
        assert_eq!(strengthened, interp);
    }

    #[test]
    fn test_strengthen_with_negative_unit() {
        // I = (x1 OR x2), A has unit (-1) → strengthened = (x1 OR x2) AND NOT x1
        let interp = PropFormula::Or(Box::new(PropFormula::Var(1)), Box::new(PropFormula::Var(2)));
        let strengthened = strengthen_interpolant(&interp, &[vec![-1]]);
        // x1=false, x2=true should satisfy strengthened
        assert!(eval(&strengthened, &[(1, false), (2, true)]));
        // x1=true, x2=false: original was true, but -1 unit means NOT x1 required
        assert!(!eval(&strengthened, &[(1, true), (2, false)]));
    }

    #[test]
    fn test_strengthen_multiple_units() {
        let interp = PropFormula::Or(Box::new(PropFormula::Var(1)), Box::new(PropFormula::Var(2)));
        let strengthened = strengthen_interpolant(&interp, &[vec![1], vec![2]]);
        // Both x1=true, x2=true must hold
        assert!(eval(&strengthened, &[(1, true), (2, true)]));
        assert!(!eval(&strengthened, &[(1, false), (2, true)]));
    }

    // --- weaken_interpolant tests ---

    #[test]
    fn test_weaken_with_matching_unit() {
        // I = x1, B has unit (-1) → weakened = x1 OR x1 = x1
        // (negation of -1 is x1)
        let interp = PropFormula::Var(1);
        let weakened = weaken_interpolant(&interp, &[vec![-1]]);
        assert!(eval(&weakened, &[(1, true)]));
    }

    #[test]
    fn test_weaken_with_positive_b_unit() {
        // I = x1, B has unit (1) → weakened = x1 OR NOT x1 (tautology)
        // simplify() does constant folding but not x OR NOT x elimination
        let interp = PropFormula::Var(1);
        let weakened = weaken_interpolant(&interp, &[vec![1]]);
        // Verify tautology by evaluating under both assignments
        assert!(eval(&weakened, &[(1, true)]));
        assert!(eval(&weakened, &[(1, false)]));
    }

    #[test]
    fn test_weaken_no_matching_units() {
        let interp = PropFormula::Var(1);
        let weakened = weaken_interpolant(&interp, &[vec![2, 3]]);
        assert_eq!(weakened, interp);
    }

    #[test]
    fn test_weaken_is_logically_weaker() {
        // I = (x1 AND x2), B has unit (-2) → weakened = (x1 AND x2) OR x2
        let interp =
            PropFormula::AndType(Box::new(PropFormula::Var(1)), Box::new(PropFormula::Var(2)));
        let weakened = weaken_interpolant(&interp, &[vec![-2]]);
        // x1=false, x2=true: original false, weakened true (x2 disjunct)
        assert!(!eval(&interp, &[(1, false), (2, true)]));
        assert!(eval(&weakened, &[(1, false), (2, true)]));
    }

    // --- verify_interpolant_property tests ---

    #[test]
    fn test_verify_valid_interpolant() {
        // A = {(1)}, B = {(-1)}, I = x1
        let interp = PropFormula::Var(1);
        let result = verify_interpolant_property(&interp, &[vec![1]], &[vec![-1]], 1);
        assert!(result.a_implies_i);
        assert!(result.i_and_b_unsat);
        assert!(result.vars_shared);
        assert!(result.valid);
    }

    #[test]
    fn test_verify_a_not_implies_i() {
        // A = {(1)}, B = {(-1)}, I = NOT x1
        let interp = PropFormula::Not(Box::new(PropFormula::Var(1)));
        let result = verify_interpolant_property(&interp, &[vec![1]], &[vec![-1]], 1);
        assert!(!result.a_implies_i);
        assert!(!result.valid);
    }

    #[test]
    fn test_verify_i_and_b_sat() {
        // A = {(1,2)}, B = {(-1)}, I = x2 (not shared — var 2 only in A)
        // But I AND B can be sat: x1=false, x2=true
        let interp = PropFormula::Var(2);
        let result = verify_interpolant_property(&interp, &[vec![1, 2]], &[vec![-1]], 2);
        assert!(!result.i_and_b_unsat);
        assert!(!result.vars_shared);
        assert!(!result.valid);
    }

    #[test]
    fn test_verify_vars_not_shared() {
        // A = {(1)}, B = {(-2)}, I = x1 — var 1 not in B
        let interp = PropFormula::Var(1);
        let result = verify_interpolant_property(&interp, &[vec![1]], &[vec![-2]], 2);
        assert!(!result.vars_shared);
        assert!(!result.valid);
    }

    #[test]
    fn test_verify_true_interpolant() {
        // I = True: A implies True (always), True AND B = B (sat if B sat)
        let interp = PropFormula::True;
        let result = verify_interpolant_property(&interp, &[vec![1]], &[vec![-1]], 1);
        assert!(result.a_implies_i);
        // True AND {-1} is satisfiable (x1=false), so not valid
        assert!(!result.i_and_b_unsat);
    }

    #[test]
    fn test_verify_false_interpolant() {
        // I = False: False AND B is always unsat, but A does not imply False
        let interp = PropFormula::False;
        let result = verify_interpolant_property(&interp, &[vec![1]], &[vec![-1]], 1);
        assert!(!result.a_implies_i);
        assert!(result.i_and_b_unsat);
    }

    #[test]
    fn test_verify_two_var_valid() {
        // A = {(1, 2)}, B = {(-1), (-2)}, I = (x1 OR x2)
        let interp = PropFormula::Or(Box::new(PropFormula::Var(1)), Box::new(PropFormula::Var(2)));
        let result = verify_interpolant_property(&interp, &[vec![1, 2]], &[vec![-1], vec![-2]], 2);
        assert!(result.valid, "should be a valid interpolant: {result:?}");
    }

    // --- count_interpolant_models tests ---

    #[test]
    fn test_count_models_true() {
        assert_eq!(count_interpolant_models(&PropFormula::True, 3), 8);
    }

    #[test]
    fn test_count_models_false() {
        assert_eq!(count_interpolant_models(&PropFormula::False, 3), 0);
    }

    #[test]
    fn test_count_models_single_var() {
        // x1: true when x1=true, half of 2^3 = 4
        assert_eq!(count_interpolant_models(&PropFormula::Var(1), 3), 4);
    }

    #[test]
    fn test_count_models_and() {
        // x1 AND x2: true when both true, 2^1 = 2 (for 3 vars)
        let f = PropFormula::AndType(Box::new(PropFormula::Var(1)), Box::new(PropFormula::Var(2)));
        assert_eq!(count_interpolant_models(&f, 3), 2);
    }

    #[test]
    fn test_count_models_or() {
        // x1 OR x2: 6 out of 8 for 3 vars
        let f = PropFormula::Or(Box::new(PropFormula::Var(1)), Box::new(PropFormula::Var(2)));
        assert_eq!(count_interpolant_models(&f, 3), 6);
    }

    #[test]
    fn test_count_models_zero_vars() {
        // True with 0 vars: 1 assignment (empty), formula is true
        assert_eq!(count_interpolant_models(&PropFormula::True, 0), 1);
        assert_eq!(count_interpolant_models(&PropFormula::False, 0), 0);
    }

    // --- interpolant_size tests ---

    #[test]
    fn test_size_var() {
        assert_eq!(interpolant_size(&PropFormula::Var(1)), 1);
    }

    #[test]
    fn test_size_constants() {
        assert_eq!(interpolant_size(&PropFormula::True), 1);
        assert_eq!(interpolant_size(&PropFormula::False), 1);
    }

    #[test]
    fn test_size_not() {
        let f = PropFormula::Not(Box::new(PropFormula::Var(1)));
        assert_eq!(interpolant_size(&f), 2);
    }

    #[test]
    fn test_size_binary() {
        // (x1 AND x2) = 3 nodes: AND, Var(1), Var(2)
        let f = PropFormula::AndType(Box::new(PropFormula::Var(1)), Box::new(PropFormula::Var(2)));
        assert_eq!(interpolant_size(&f), 3);
    }

    #[test]
    fn test_size_nested() {
        // NOT (x1 OR x2) = 4 nodes: NOT, OR, Var(1), Var(2)
        let f = PropFormula::Not(Box::new(PropFormula::Or(
            Box::new(PropFormula::Var(1)),
            Box::new(PropFormula::Var(2)),
        )));
        assert_eq!(interpolant_size(&f), 4);
    }

    #[test]
    fn test_size_implies() {
        // (x1 -> x2) = 3 nodes
        let f = PropFormula::Implies(Box::new(PropFormula::Var(1)), Box::new(PropFormula::Var(2)));
        assert_eq!(interpolant_size(&f), 3);
    }

    // --- NodeKind and InterpolantVerifyResult type tests ---

    #[test]
    fn test_node_kind_debug() {
        let input = NodeKind::Input(0);
        let resolve = NodeKind::Resolve {
            left: 0,
            right: 1,
            pivot: 1,
        };
        let _ = format!("{input:?}");
        let _ = format!("{resolve:?}");
    }

    #[test]
    fn test_interpolant_verify_result_fields() {
        let result = InterpolantVerifyResult {
            a_implies_i: true,
            i_and_b_unsat: true,
            vars_shared: true,
            valid: true,
        };
        assert!(result.valid);
        assert_eq!(result, result);
    }
}
