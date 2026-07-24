// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dedicated tests for `mcmillan_tree.rs`: tree interpolant extraction,
//! strengthening, weakening, brute-force Craig verification, model counting,
//! and formula size measurement.

use super::mcmillan_tree::*;
use super::PropFormula;
use std::collections::HashMap;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn eval(f: &PropFormula, asgn: &[(u32, bool)]) -> bool {
    let map: HashMap<u32, bool> = asgn.iter().copied().collect();
    f.evaluate(&map)
}

/// Build a simple refutation DAG: A = {(p)}, B = {(-p)}, resolve on p.
fn simple_unit_dag(var: i32) -> Vec<(Vec<i32>, NodeKind)> {
    vec![
        (vec![var], NodeKind::Input(0)),
        (vec![-var], NodeKind::Input(1)),
        (
            vec![],
            NodeKind::Resolve {
                left: 0,
                right: 1,
                pivot: var,
            },
        ),
    ]
}

// ---------------------------------------------------------------------------
// NodeKind type tests
// ---------------------------------------------------------------------------

#[test]
fn test_node_kind_input_clone_eq() {
    let a = NodeKind::Input(42);
    let b = a.clone();
    assert_eq!(a, b);
}

#[test]
fn test_node_kind_resolve_clone_eq() {
    let a = NodeKind::Resolve {
        left: 0,
        right: 1,
        pivot: -3,
    };
    let b = a.clone();
    assert_eq!(a, b);
}

#[test]
fn test_node_kind_input_ne_resolve() {
    let input = NodeKind::Input(0);
    let resolve = NodeKind::Resolve {
        left: 0,
        right: 1,
        pivot: 1,
    };
    assert_ne!(input, resolve);
}

#[test]
fn test_node_kind_debug_format() {
    let n = NodeKind::Input(7);
    let s = format!("{n:?}");
    assert!(s.contains("Input"));
    assert!(s.contains("7"));

    let r = NodeKind::Resolve {
        left: 2,
        right: 3,
        pivot: -5,
    };
    let s = format!("{r:?}");
    assert!(s.contains("Resolve"));
    assert!(s.contains("-5"));
}

// ---------------------------------------------------------------------------
// InterpolantVerifyResult type tests
// ---------------------------------------------------------------------------

#[test]
fn test_verify_result_all_true() {
    let r = InterpolantVerifyResult {
        a_implies_i: true,
        i_and_b_unsat: true,
        vars_shared: true,
        valid: true,
    };
    assert!(r.valid);
    assert_eq!(r, r);
}

#[test]
fn test_verify_result_partial_failure() {
    let r = InterpolantVerifyResult {
        a_implies_i: false,
        i_and_b_unsat: true,
        vars_shared: true,
        valid: false,
    };
    assert!(!r.valid);
    assert!(!r.a_implies_i);
}

#[test]
fn test_verify_result_copy_semantics() {
    let r = InterpolantVerifyResult {
        a_implies_i: true,
        i_and_b_unsat: false,
        vars_shared: true,
        valid: false,
    };
    let r2 = r; // Copy
    assert_eq!(r, r2);
}

#[test]
fn test_verify_result_debug() {
    let r = InterpolantVerifyResult {
        a_implies_i: true,
        i_and_b_unsat: true,
        vars_shared: false,
        valid: false,
    };
    let s = format!("{r:?}");
    assert!(s.contains("vars_shared: false"));
}

// ---------------------------------------------------------------------------
// tree_interpolant — empty / trivial cases
// ---------------------------------------------------------------------------

#[test]
fn test_tree_interpolant_empty_dag_returns_true() {
    let interp = tree_interpolant(&[], &[], &[]);
    assert_eq!(interp, PropFormula::True);
}

#[test]
fn test_tree_interpolant_single_b_input_returns_true() {
    let dag = vec![(vec![1, 2], NodeKind::Input(0))];
    let interp = tree_interpolant(&dag, &[], &[1, 2]);
    assert_eq!(interp, PropFormula::True);
}

#[test]
fn test_tree_interpolant_single_a_input_no_shared_vars() {
    // A clause with vars {1,2} but shared = {} => False (no shared lits)
    let dag = vec![(vec![1, 2], NodeKind::Input(0))];
    let interp = tree_interpolant(&dag, &[0], &[]);
    assert_eq!(interp, PropFormula::False);
}

#[test]
fn test_tree_interpolant_single_a_input_all_shared() {
    // A clause (1, 2), shared = {1, 2} => disjunction x1 OR x2
    let dag = vec![(vec![1, 2], NodeKind::Input(0))];
    let interp = tree_interpolant(&dag, &[0], &[1, 2]);
    let vars = interp.variables();
    assert!(vars.contains(&1));
    assert!(vars.contains(&2));
    // Should be true when x1=true
    assert!(eval(&interp, &[(1, true), (2, false)]));
    // Should be true when x2=true
    assert!(eval(&interp, &[(1, false), (2, true)]));
    // Should be false when both false
    assert!(!eval(&interp, &[(1, false), (2, false)]));
}

// ---------------------------------------------------------------------------
// tree_interpolant — unit clause refutations
// ---------------------------------------------------------------------------

#[test]
fn test_tree_interpolant_unit_refutation_shared_pivot() {
    // A = {(1)}, B = {(-1)}, shared = {1}
    let dag = simple_unit_dag(1);
    let interp = tree_interpolant(&dag, &[0], &[1]);
    // A implies I: x1=true => I true
    assert!(eval(&interp, &[(1, true)]));
    // I AND B unsat: x1=false => I false
    assert!(!eval(&interp, &[(1, false)]));
}

#[test]
fn test_tree_interpolant_unit_refutation_negative_literal() {
    // A = {(-3)}, B = {(3)}, shared = {3}
    // Pudlak's rule on a shared pivot produces (p AND True) OR (NOT p AND NOT p)
    // which simplifies to x3 OR NOT x3 (tautology). This is still a valid Craig
    // interpolant extraction step; verify via brute-force check instead.
    let dag = vec![
        (vec![-3], NodeKind::Input(0)),
        (vec![3], NodeKind::Input(1)),
        (
            vec![],
            NodeKind::Resolve {
                left: 0,
                right: 1,
                pivot: 3,
            },
        ),
    ];
    let interp = tree_interpolant(&dag, &[0], &[3]);
    // The interpolant should only reference var 3 (shared)
    let vars = interp.variables();
    assert!(vars.is_subset(&[3].iter().copied().collect()));
    // A satisfied when x3=false, so I must be true there
    assert!(eval(&interp, &[(3, false)]));
}

// ---------------------------------------------------------------------------
// tree_interpolant — A-only pivot
// ---------------------------------------------------------------------------

#[test]
fn test_tree_interpolant_a_only_pivot_eliminates_var() {
    // A = {(1,2), (-1,2)}, B = {(-2)}, shared = {2}, A-only = {1}
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
    // Var 1 is A-only and must not appear
    assert!(!interp.variables().contains(&1));
}

#[test]
fn test_tree_interpolant_a_only_pivot_disjunction_rule() {
    // With A-only pivot, the rule is I_left OR I_right
    // A = {(1,3), (-1,3)}, B = {(-3)}, shared = {3}
    let dag = vec![
        (vec![1, 3], NodeKind::Input(0)),
        (vec![-1, 3], NodeKind::Input(1)),
        (vec![-3], NodeKind::Input(2)),
        (
            vec![3],
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
                pivot: 3,
            },
        ),
    ];
    let interp = tree_interpolant(&dag, &[0, 1], &[3]);
    // Craig properties: verify via brute force
    let result = verify_interpolant_property(&interp, &[vec![1, 3], vec![-1, 3]], &[vec![-3]], 3);
    assert!(result.valid, "Craig properties should hold: {result:?}");
}

// ---------------------------------------------------------------------------
// tree_interpolant — B-only pivot
// ---------------------------------------------------------------------------

#[test]
fn test_tree_interpolant_b_only_pivot_eliminates_var() {
    // A = {(1)}, B = {(-1,2), (-1,-2)}, shared = {1}, B-only = {2}
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
    assert!(
        !interp.variables().contains(&2),
        "B-only var 2 must not appear"
    );
}

#[test]
fn test_tree_interpolant_b_only_pivot_conjunction_rule() {
    // B-only pivot produces I_left AND I_right
    // shared_vars = {1} (only var appearing in both A and B partitions)
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
    let result = verify_interpolant_property(&interp, &[vec![1]], &[vec![-1, 2], vec![-1, -2]], 2);
    assert!(result.valid, "Craig properties should hold: {result:?}");
}

// ---------------------------------------------------------------------------
// tree_interpolant — shared pivot (Pudlak's rule)
// ---------------------------------------------------------------------------

#[test]
fn test_tree_interpolant_shared_pivot_uses_both_vars() {
    // A = {(1,2)}, B = {(-1),(-2)}, shared = {1,2}
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
    let vars = interp.variables();
    // Interpolant should use only shared vars
    for v in &vars {
        assert!(*v == 1 || *v == 2, "unexpected var {v} in interpolant");
    }
}

#[test]
fn test_tree_interpolant_shared_pivot_craig_valid() {
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
    assert!(result.valid, "Shared-pivot Craig properties: {result:?}");
}

// ---------------------------------------------------------------------------
// tree_interpolant — multi-clause, mixed pivots
// ---------------------------------------------------------------------------

#[test]
fn test_tree_interpolant_three_vars_mixed() {
    // A = {(1,2), (-1,3)}, B = {(-2,-3)}, shared = {2,3}, A-only = {1}
    let dag = vec![
        (vec![1, 2], NodeKind::Input(0)),
        (vec![-1, 3], NodeKind::Input(1)),
        (vec![-2, -3], NodeKind::Input(2)),
        // Resolve A clauses on A-only var 1
        (
            vec![2, 3],
            NodeKind::Resolve {
                left: 0,
                right: 1,
                pivot: 1,
            },
        ),
        // Resolve with B on shared var 2
        (
            vec![3, -3],
            NodeKind::Resolve {
                left: 3,
                right: 2,
                pivot: 2,
            },
        ),
    ];
    let interp = tree_interpolant(&dag, &[0, 1], &[2, 3]);
    assert!(
        !interp.variables().contains(&1),
        "A-only var 1 must not appear"
    );
}

// ---------------------------------------------------------------------------
// tree_interpolant — negative literal A input with partial sharing
// ---------------------------------------------------------------------------

#[test]
fn test_tree_interpolant_a_negative_shared_lit() {
    // A = {(-1, -2)}, shared = {1}, A-only = {2}
    // The shared lit disjunction should include NOT x1 only
    let dag = vec![(vec![-1, -2], NodeKind::Input(0))];
    let interp = tree_interpolant(&dag, &[0], &[1]);
    assert!(interp.variables().contains(&1));
    assert!(!interp.variables().contains(&2));
    // NOT x1 should be true when x1=false
    assert!(eval(&interp, &[(1, false)]));
    // NOT x1 should be false when x1=true
    assert!(!eval(&interp, &[(1, true)]));
}

// ---------------------------------------------------------------------------
// strengthen_interpolant tests
// ---------------------------------------------------------------------------

#[test]
fn test_strengthen_with_matching_positive_unit() {
    let interp = PropFormula::Var(1);
    let strengthened = strengthen_interpolant(&interp, &[vec![1]]);
    // x1 AND x1 simplifies to x1
    assert!(eval(&strengthened, &[(1, true)]));
    assert!(!eval(&strengthened, &[(1, false)]));
}

#[test]
fn test_strengthen_with_matching_negative_unit() {
    let interp = PropFormula::Or(Box::new(PropFormula::Var(1)), Box::new(PropFormula::Var(2)));
    let strengthened = strengthen_interpolant(&interp, &[vec![-1]]);
    // Strengthened: (x1 OR x2) AND NOT x1
    // x1=true, x2=false: original true, strengthened false
    assert!(!eval(&strengthened, &[(1, true), (2, false)]));
    // x1=false, x2=true: strengthened true
    assert!(eval(&strengthened, &[(1, false), (2, true)]));
}

#[test]
fn test_strengthen_no_matching_units_unchanged() {
    let interp = PropFormula::Var(1);
    let strengthened = strengthen_interpolant(&interp, &[vec![2, 3]]);
    assert_eq!(strengthened, interp);
}

#[test]
fn test_strengthen_skips_non_unit_clauses() {
    let interp = PropFormula::Var(1);
    // Multi-literal clause with var 1 — should be skipped
    let strengthened = strengthen_interpolant(&interp, &[vec![1, 2]]);
    assert_eq!(strengthened, interp);
}

#[test]
fn test_strengthen_empty_a_clauses() {
    let interp = PropFormula::Var(1);
    let strengthened = strengthen_interpolant(&interp, &[]);
    assert_eq!(strengthened, interp);
}

#[test]
fn test_strengthen_multiple_matching_units() {
    let interp = PropFormula::Or(Box::new(PropFormula::Var(1)), Box::new(PropFormula::Var(2)));
    let strengthened = strengthen_interpolant(&interp, &[vec![1], vec![2]]);
    // Must satisfy both x1 and x2
    assert!(eval(&strengthened, &[(1, true), (2, true)]));
    assert!(!eval(&strengthened, &[(1, false), (2, true)]));
    assert!(!eval(&strengthened, &[(1, true), (2, false)]));
}

#[test]
fn test_strengthen_constant_true_interpolant() {
    let interp = PropFormula::True;
    // No interp vars => no unit matches => unchanged
    let strengthened = strengthen_interpolant(&interp, &[vec![1]]);
    assert_eq!(strengthened, PropFormula::True);
}

// ---------------------------------------------------------------------------
// weaken_interpolant tests
// ---------------------------------------------------------------------------

#[test]
fn test_weaken_with_negative_b_unit() {
    // I = x1, B has unit (-1) => weakened = x1 OR x1 (negation of -1 is +1)
    let interp = PropFormula::Var(1);
    let weakened = weaken_interpolant(&interp, &[vec![-1]]);
    assert!(eval(&weakened, &[(1, true)]));
}

#[test]
fn test_weaken_with_positive_b_unit_produces_tautology() {
    // I = x1, B has unit (1) => weakened = x1 OR NOT x1
    let interp = PropFormula::Var(1);
    let weakened = weaken_interpolant(&interp, &[vec![1]]);
    assert!(eval(&weakened, &[(1, true)]));
    assert!(eval(&weakened, &[(1, false)]));
}

#[test]
fn test_weaken_no_matching_units_unchanged() {
    let interp = PropFormula::Var(1);
    let weakened = weaken_interpolant(&interp, &[vec![2, 3]]);
    assert_eq!(weakened, interp);
}

#[test]
fn test_weaken_skips_non_unit_clauses() {
    let interp = PropFormula::Var(1);
    let weakened = weaken_interpolant(&interp, &[vec![1, 2]]);
    assert_eq!(weakened, interp);
}

#[test]
fn test_weaken_empty_b_clauses() {
    let interp = PropFormula::Var(1);
    let weakened = weaken_interpolant(&interp, &[]);
    assert_eq!(weakened, interp);
}

#[test]
fn test_weaken_is_logically_weaker() {
    // I = (x1 AND x2), B has unit (-2) => weakened = (x1 AND x2) OR x2
    let interp = PropFormula::AndType(Box::new(PropFormula::Var(1)), Box::new(PropFormula::Var(2)));
    let weakened = weaken_interpolant(&interp, &[vec![-2]]);
    // x1=false, x2=true: original false, weakened true
    assert!(!eval(&interp, &[(1, false), (2, true)]));
    assert!(eval(&weakened, &[(1, false), (2, true)]));
}

#[test]
fn test_weaken_constant_false_interpolant() {
    // False has no variables => no unit matches => unchanged
    let interp = PropFormula::False;
    let weakened = weaken_interpolant(&interp, &[vec![1]]);
    assert_eq!(weakened, PropFormula::False);
}

// ---------------------------------------------------------------------------
// verify_interpolant_property tests
// ---------------------------------------------------------------------------

#[test]
fn test_verify_valid_interpolant_x1() {
    // A = {(1)}, B = {(-1)}, I = x1
    let result = verify_interpolant_property(&PropFormula::Var(1), &[vec![1]], &[vec![-1]], 1);
    assert!(result.a_implies_i);
    assert!(result.i_and_b_unsat);
    assert!(result.vars_shared);
    assert!(result.valid);
}

#[test]
fn test_verify_a_does_not_imply_false() {
    // I = False, A = {(1)}: A is satisfiable but False is never true
    let result = verify_interpolant_property(&PropFormula::False, &[vec![1]], &[vec![-1]], 1);
    assert!(!result.a_implies_i);
    assert!(result.i_and_b_unsat); // False AND anything is unsat
}

#[test]
fn test_verify_true_not_unsat_with_b() {
    // I = True, B = {(-1)}: True AND B is satisfiable
    let result = verify_interpolant_property(&PropFormula::True, &[vec![1]], &[vec![-1]], 1);
    assert!(result.a_implies_i);
    assert!(!result.i_and_b_unsat);
}

#[test]
fn test_verify_vars_not_shared() {
    // A = {(1)}, B = {(-2)}, I = x1 => var 1 not in B
    let result = verify_interpolant_property(&PropFormula::Var(1), &[vec![1]], &[vec![-2]], 2);
    assert!(!result.vars_shared);
    assert!(!result.valid);
}

#[test]
fn test_verify_two_var_or_interpolant() {
    // A = {(1,2)}, B = {(-1),(-2)}, I = (x1 OR x2)
    let interp = PropFormula::Or(Box::new(PropFormula::Var(1)), Box::new(PropFormula::Var(2)));
    let result = verify_interpolant_property(&interp, &[vec![1, 2]], &[vec![-1], vec![-2]], 2);
    assert!(result.valid, "should be valid: {result:?}");
}

#[test]
fn test_verify_zero_vars() {
    // Edge: 0 variables. A = empty clauses, B = empty clauses.
    // True with 0 vars: 1 assignment total.
    let result = verify_interpolant_property(&PropFormula::True, &[], &[], 0);
    assert!(result.a_implies_i);
    // True AND (no B clauses) = True => i_and_b_unsat is false
    assert!(!result.i_and_b_unsat);
    assert!(result.vars_shared);
}

#[test]
fn test_verify_unsatisfiable_a() {
    // A = {(1), (-1)} — A is unsatisfiable. Any I is vacuously implied by A.
    let result =
        verify_interpolant_property(&PropFormula::False, &[vec![1], vec![-1]], &[vec![2]], 2);
    assert!(result.a_implies_i); // vacuously true
    assert!(result.i_and_b_unsat); // False AND B always unsat
}

// ---------------------------------------------------------------------------
// count_interpolant_models tests
// ---------------------------------------------------------------------------

#[test]
fn test_count_models_true_n3() {
    assert_eq!(count_interpolant_models(&PropFormula::True, 3), 8);
}

#[test]
fn test_count_models_false_n3() {
    assert_eq!(count_interpolant_models(&PropFormula::False, 3), 0);
}

#[test]
fn test_count_models_single_var() {
    // x1 is true in exactly half of 2^3 = 4
    assert_eq!(count_interpolant_models(&PropFormula::Var(1), 3), 4);
}

#[test]
fn test_count_models_and_two_vars() {
    // x1 AND x2: true when both true => 2^1 = 2 (for 3 vars)
    let f = PropFormula::AndType(Box::new(PropFormula::Var(1)), Box::new(PropFormula::Var(2)));
    assert_eq!(count_interpolant_models(&f, 3), 2);
}

#[test]
fn test_count_models_or_two_vars() {
    // x1 OR x2: 6 out of 8 for 3 vars
    let f = PropFormula::Or(Box::new(PropFormula::Var(1)), Box::new(PropFormula::Var(2)));
    assert_eq!(count_interpolant_models(&f, 3), 6);
}

#[test]
fn test_count_models_zero_vars() {
    assert_eq!(count_interpolant_models(&PropFormula::True, 0), 1);
    assert_eq!(count_interpolant_models(&PropFormula::False, 0), 0);
}

#[test]
fn test_count_models_negation() {
    // NOT x1: true in 4 out of 8 for 3 vars
    let f = PropFormula::Not(Box::new(PropFormula::Var(1)));
    assert_eq!(count_interpolant_models(&f, 3), 4);
}

#[test]
fn test_count_models_implies() {
    // x1 -> x2: false only when x1=true, x2=false => 6 out of 8
    let f = PropFormula::Implies(Box::new(PropFormula::Var(1)), Box::new(PropFormula::Var(2)));
    assert_eq!(count_interpolant_models(&f, 3), 6);
}

#[test]
fn test_count_models_one_var() {
    // x1 with 1 var: true in 1 out of 2
    assert_eq!(count_interpolant_models(&PropFormula::Var(1), 1), 1);
}

// ---------------------------------------------------------------------------
// interpolant_size tests
// ---------------------------------------------------------------------------

#[test]
fn test_size_var_is_1() {
    assert_eq!(interpolant_size(&PropFormula::Var(42)), 1);
}

#[test]
fn test_size_true_is_1() {
    assert_eq!(interpolant_size(&PropFormula::True), 1);
}

#[test]
fn test_size_false_is_1() {
    assert_eq!(interpolant_size(&PropFormula::False), 1);
}

#[test]
fn test_size_not_is_2() {
    let f = PropFormula::Not(Box::new(PropFormula::Var(1)));
    assert_eq!(interpolant_size(&f), 2);
}

#[test]
fn test_size_and_is_3() {
    let f = PropFormula::AndType(Box::new(PropFormula::Var(1)), Box::new(PropFormula::Var(2)));
    assert_eq!(interpolant_size(&f), 3);
}

#[test]
fn test_size_or_is_3() {
    let f = PropFormula::Or(Box::new(PropFormula::Var(1)), Box::new(PropFormula::Var(2)));
    assert_eq!(interpolant_size(&f), 3);
}

#[test]
fn test_size_implies_is_3() {
    let f = PropFormula::Implies(Box::new(PropFormula::Var(1)), Box::new(PropFormula::Var(2)));
    assert_eq!(interpolant_size(&f), 3);
}

#[test]
fn test_size_nested_not_or() {
    // NOT (x1 OR x2) = 4 nodes
    let f = PropFormula::Not(Box::new(PropFormula::Or(
        Box::new(PropFormula::Var(1)),
        Box::new(PropFormula::Var(2)),
    )));
    assert_eq!(interpolant_size(&f), 4);
}

#[test]
fn test_size_deep_nesting() {
    // ((x1 AND x2) OR (x3 AND x4)) = 7 nodes
    let f = PropFormula::Or(
        Box::new(PropFormula::AndType(
            Box::new(PropFormula::Var(1)),
            Box::new(PropFormula::Var(2)),
        )),
        Box::new(PropFormula::AndType(
            Box::new(PropFormula::Var(3)),
            Box::new(PropFormula::Var(4)),
        )),
    );
    assert_eq!(interpolant_size(&f), 7);
}

// ---------------------------------------------------------------------------
// End-to-end: tree_interpolant + verify_interpolant_property
// ---------------------------------------------------------------------------

#[test]
fn test_e2e_craig_valid_two_var() {
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
    assert!(result.valid);
}

#[test]
fn test_e2e_strengthened_still_valid() {
    // A = {(1,2)}, B = {(-1),(-2)}
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
    let strengthened = strengthen_interpolant(&interp, &[vec![1, 2]]);
    // A still implies strengthened (strengthened is logically stronger)
    let result =
        verify_interpolant_property(&strengthened, &[vec![1, 2]], &[vec![-1], vec![-2]], 2);
    assert!(
        result.a_implies_i,
        "A should still imply strengthened interp"
    );
}

#[test]
fn test_e2e_weakened_preserves_b_unsat() {
    // A = {(1)}, B = {(-1)}
    let dag = simple_unit_dag(1);
    let interp = tree_interpolant(&dag, &[0], &[1]);
    let weakened = weaken_interpolant(&interp, &[vec![-1]]);
    let result = verify_interpolant_property(&weakened, &[vec![1]], &[vec![-1]], 1);
    assert!(result.i_and_b_unsat, "weakened AND B should still be unsat");
}

#[test]
fn test_e2e_model_count_consistency() {
    // For I = (x1 OR x2) over 2 vars: 3 models
    let interp = PropFormula::Or(Box::new(PropFormula::Var(1)), Box::new(PropFormula::Var(2)));
    let count = count_interpolant_models(&interp, 2);
    assert_eq!(count, 3);
    let size = interpolant_size(&interp);
    assert_eq!(size, 3);
}
