// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Craig interpolation property verification.

use super::property::{
    compute_shared_variables, enumerate_satisfying_assignments, evaluate_formula,
    extract_variables, interpolant_size_info, verify_all_properties, verify_contradiction,
    verify_implication, verify_interpolant_strength, verify_variable_restriction,
    InterpolantProperty, InterpolantSizeInfo, InterpolantStrengthClass,
    I10_INTERPOLANT_IMPLICATION, I11_INTERPOLANT_CONTRADICTION, I12_INTERPOLANT_VARIABLES,
};
use super::PropFormula;
use crate::spec::ProofStatus;
use std::collections::HashMap;

fn var(v: u32) -> PropFormula {
    PropFormula::Var(v)
}
fn not(f: PropFormula) -> PropFormula {
    PropFormula::Not(Box::new(f))
}
fn and(l: PropFormula, r: PropFormula) -> PropFormula {
    PropFormula::AndType(Box::new(l), Box::new(r))
}
fn or(l: PropFormula, r: PropFormula) -> PropFormula {
    PropFormula::Or(Box::new(l), Box::new(r))
}

#[test]
fn test_proof_status_constants_values() {
    assert_eq!(I10_INTERPOLANT_IMPLICATION, ProofStatus::DerivedPending);
    assert_eq!(I11_INTERPOLANT_CONTRADICTION, ProofStatus::DerivedPending);
    assert_eq!(I12_INTERPOLANT_VARIABLES, ProofStatus::DerivedPending);
}

#[test]
fn test_interpolant_property_variants_distinct() {
    assert_ne!(
        InterpolantProperty::Implication,
        InterpolantProperty::Contradiction
    );
    assert_ne!(
        InterpolantProperty::Contradiction,
        InterpolantProperty::VariableRestriction
    );
    assert_ne!(
        InterpolantProperty::Implication,
        InterpolantProperty::VariableRestriction
    );
}

#[test]
fn test_extract_variables_basic() {
    let vars = extract_variables(&[vec![1, -2], vec![3]]);
    assert_eq!(vars.len(), 3);
    assert!(vars.contains(&1) && vars.contains(&2) && vars.contains(&3));
}

#[test]
fn test_extract_variables_empty() {
    assert!(extract_variables(&[]).is_empty());
}

#[test]
fn test_extract_variables_duplicate_vars() {
    let vars = extract_variables(&[vec![1, -1], vec![1, 2]]);
    assert_eq!(vars.len(), 2);
}

#[test]
fn test_shared_variables_overlap() {
    let shared = compute_shared_variables(&[vec![1, 2]], &[vec![2, 3]]);
    assert_eq!(shared.len(), 1);
    assert!(shared.contains(&2));
}

#[test]
fn test_shared_variables_no_overlap() {
    assert!(compute_shared_variables(&[vec![1]], &[vec![2]]).is_empty());
}

#[test]
fn test_shared_variables_full_overlap() {
    let shared = compute_shared_variables(&[vec![1, 2, 3]], &[vec![1, -2, 3]]);
    assert_eq!(shared.len(), 3);
}

#[test]
fn test_evaluate_formula_satisfied() {
    let clauses = vec![vec![1, 2], vec![-1, 3]];
    let mut asgn = HashMap::new();
    asgn.insert(1, true);
    asgn.insert(2, false);
    asgn.insert(3, true);
    assert!(evaluate_formula(&clauses, &asgn));
}

#[test]
fn test_evaluate_formula_unsatisfied() {
    let mut asgn = HashMap::new();
    asgn.insert(1, true);
    assert!(!evaluate_formula(&[vec![1], vec![-1]], &asgn));
}

#[test]
fn test_evaluate_formula_empty_is_true() {
    assert!(evaluate_formula(&[], &HashMap::new()));
}

#[test]
fn test_enumerate_satisfying_single_var_unit() {
    let assignments = enumerate_satisfying_assignments(&[vec![1]], 1);
    assert_eq!(assignments.len(), 1);
    assert!(assignments[0][&1]);
}

#[test]
fn test_enumerate_satisfying_tautology() {
    let assignments = enumerate_satisfying_assignments(&[vec![1, -1]], 1);
    assert_eq!(assignments.len(), 2);
}

#[test]
fn test_enumerate_satisfying_unsat() {
    assert!(enumerate_satisfying_assignments(&[vec![1], vec![-1]], 1).is_empty());
}

#[test]
fn test_enumerate_satisfying_two_vars() {
    let assignments = enumerate_satisfying_assignments(&[vec![1], vec![2]], 2);
    assert_eq!(assignments.len(), 1);
    assert!(assignments[0][&1] && assignments[0][&2]);
}

#[test]
fn test_implication_correct_interpolant() {
    let a = vec![vec![1, 2]];
    assert!(verify_implication(&a, &or(var(1), var(2)), 2).is_ok());
}

#[test]
fn test_implication_too_strong_interpolant() {
    // A = {(x1, x2)}, I = x1. x1=F, x2=T satisfies A but not I.
    let result = verify_implication(&[vec![1, 2]], &var(1), 2);
    assert!(result.is_err());
    let cex = result.unwrap_err();
    assert!(!cex[&1]);
    assert!(cex[&2]);
}

#[test]
fn test_implication_true_interpolant() {
    assert!(verify_implication(&[vec![1]], &PropFormula::True, 1).is_ok());
}

#[test]
fn test_implication_false_interpolant_fails_for_sat_a() {
    assert!(verify_implication(&[vec![1]], &PropFormula::False, 1).is_err());
}

#[test]
fn test_implication_empty_a() {
    let a: Vec<Vec<i32>> = vec![];
    assert!(verify_implication(&a, &PropFormula::True, 2).is_ok());
    assert!(verify_implication(&a, &PropFormula::False, 2).is_err());
}

#[test]
fn test_contradiction_correct() {
    assert!(verify_contradiction(&[vec![1]], &not(var(1)), 1).is_ok());
}

#[test]
fn test_contradiction_fails() {
    let result = verify_contradiction(&[vec![1]], &var(1), 1);
    assert!(result.is_err());
    assert!(result.unwrap_err()[&1]);
}

#[test]
fn test_contradiction_false_interpolant() {
    assert!(verify_contradiction(&[vec![1, 2]], &PropFormula::False, 2).is_ok());
}

#[test]
fn test_contradiction_empty_b() {
    let b: Vec<Vec<i32>> = vec![];
    assert!(verify_contradiction(&b, &PropFormula::False, 1).is_ok());
    assert!(verify_contradiction(&b, &PropFormula::True, 1).is_err());
}

#[test]
fn test_variable_restriction_valid() {
    assert!(verify_variable_restriction(&[vec![1, 2]], &[vec![2, 3]], &var(2)).is_ok());
}

#[test]
fn test_variable_restriction_violation() {
    let result = verify_variable_restriction(&[vec![1, 2]], &[vec![2, 3]], &and(var(1), var(2)));
    assert!(result.is_err());
    let violations = result.unwrap_err();
    assert!(violations.contains(&1));
    assert!(!violations.contains(&2));
}

#[test]
fn test_variable_restriction_constant_interpolant() {
    assert!(verify_variable_restriction(&[vec![1]], &[vec![2]], &PropFormula::True).is_ok());
    assert!(verify_variable_restriction(&[vec![1]], &[vec![2]], &PropFormula::False).is_ok());
}

#[test]
fn test_all_properties_correct_interpolant() {
    // A = {(x2)}, B = {(NOT x2)}. I = x2.
    let result = verify_all_properties(&[vec![2]], &[vec![-2]], &var(2), 2);
    assert!(result.implication_holds);
    assert!(result.contradiction_holds);
    assert!(result.variable_restriction_holds);
    assert!(result.all_valid);
    assert!(result.violating_variables.is_empty());
    assert!(result.implication_counterexample.is_none());
    assert!(result.contradiction_witness.is_none());
}

#[test]
fn test_all_properties_wrong_interpolant() {
    // A = {(x1)}, B = {(NOT x1)}, I = NOT x1.
    let result = verify_all_properties(&[vec![1]], &[vec![-1]], &not(var(1)), 1);
    assert!(!result.implication_holds);
    assert!(!result.all_valid);
    assert!(result.implication_counterexample.is_some());
}

#[test]
fn test_all_properties_variable_violation() {
    let result = verify_all_properties(&[vec![1]], &[vec![-1]], &var(2), 2);
    assert!(!result.variable_restriction_holds);
    assert!(!result.all_valid);
    assert!(result.violating_variables.contains(&2));
}

#[test]
fn test_all_properties_three_var_example() {
    // A = {(x1, x2), (NOT x1, x2)}, B = {(NOT x2, x3), (NOT x2, NOT x3)}
    // A simplifies to x2. B simplifies to NOT x2. I = x2 is valid.
    let a = vec![vec![1, 2], vec![-1, 2]];
    let b = vec![vec![-2, 3], vec![-2, -3]];
    assert!(verify_all_properties(&a, &b, &var(2), 3).all_valid);
}

#[test]
fn test_strength_equivalent_to_a() {
    let strength = verify_interpolant_strength(&[vec![1]], &[vec![-1]], &var(1), 1);
    assert_eq!(strength, InterpolantStrengthClass::EquivalentToA);
}

#[test]
fn test_strength_equivalent_to_not_b() {
    // A = {(x1, x2)}, B = {(NOT x2)}. NOT B = x2. I = x2 ≡ NOT B.
    let strength = verify_interpolant_strength(&[vec![1, 2]], &[vec![-2]], &var(2), 2);
    assert_eq!(strength, InterpolantStrengthClass::EquivalentToNotB);
}

#[test]
fn test_strength_trivial_true() {
    let s = verify_interpolant_strength(&[vec![1]], &[vec![-1]], &PropFormula::True, 1);
    assert_eq!(s, InterpolantStrengthClass::Trivial);
}

#[test]
fn test_strength_trivial_false() {
    let s = verify_interpolant_strength(&[vec![1]], &[vec![-1]], &PropFormula::False, 1);
    assert_eq!(s, InterpolantStrengthClass::Trivial);
}

#[test]
fn test_strength_intermediate() {
    // A = x1 AND x2, NOT B = x1 OR x2. I = x1 is intermediate.
    let s = verify_interpolant_strength(&[vec![1], vec![2]], &[vec![-1], vec![-2]], &var(1), 2);
    assert_eq!(s, InterpolantStrengthClass::Intermediate);
}

#[test]
fn test_size_info_atom() {
    let info = interpolant_size_info(&var(1));
    assert_eq!(info.node_count, 1);
    assert_eq!(info.variable_count, 1);
}

#[test]
fn test_size_info_conjunction() {
    let info = interpolant_size_info(&and(var(1), var(2)));
    assert_eq!(info.node_count, 3);
    assert_eq!(info.variable_count, 2);
}

#[test]
fn test_size_info_negation() {
    let info = interpolant_size_info(&not(var(1)));
    assert_eq!(info.node_count, 2);
    assert_eq!(info.variable_count, 1);
}

#[test]
fn test_size_info_constant() {
    let info = interpolant_size_info(&PropFormula::True);
    assert_eq!(info.node_count, 1);
    assert_eq!(info.variable_count, 0);
}

#[test]
fn test_size_info_complex() {
    // (x1 AND x2) OR (NOT x3) — 6 nodes, 3 vars
    let info = interpolant_size_info(&or(and(var(1), var(2)), not(var(3))));
    assert_eq!(info.node_count, 6);
    assert_eq!(info.variable_count, 3);
}

#[test]
fn test_single_clause_a_valid() {
    assert!(verify_all_properties(&[vec![1]], &[vec![-1]], &var(1), 1).all_valid);
}

#[test]
fn test_tautological_interpolant_true() {
    // I = True: implication OK, but contradiction fails (B is satisfiable).
    let result = verify_all_properties(&[vec![1]], &[vec![-1]], &PropFormula::True, 1);
    assert!(result.implication_holds);
    assert!(!result.contradiction_holds);
    assert!(!result.all_valid);
}

#[test]
fn test_tautological_interpolant_false() {
    // I = False: contradiction OK, but implication fails (A is satisfiable).
    let result = verify_all_properties(&[vec![1]], &[vec![-1]], &PropFormula::False, 1);
    assert!(!result.implication_holds);
    assert!(result.contradiction_holds);
    assert!(!result.all_valid);
}

#[test]
fn test_result_counterexample_is_genuine() {
    let a = vec![vec![1, 2]];
    let interp = and(var(1), var(2));
    let result = verify_all_properties(&a, &[vec![-1], vec![-2]], &interp, 2);
    assert!(!result.implication_holds);
    let cex = result
        .implication_counterexample
        .as_ref()
        .expect("counterexample");
    assert!(evaluate_formula(&a, cex));
    assert!(!interp.evaluate(cex));
}

#[test]
fn test_result_witness_is_genuine() {
    let b = vec![vec![1]];
    let interp = var(1);
    let result = verify_all_properties(&[vec![1]], &b, &interp, 1);
    assert!(!result.contradiction_holds);
    let witness = result.contradiction_witness.as_ref().expect("witness");
    assert!(evaluate_formula(&b, witness));
    assert!(interp.evaluate(witness));
}

#[test]
fn test_size_info_equality() {
    let a = InterpolantSizeInfo {
        node_count: 3,
        variable_count: 2,
    };
    let b = InterpolantSizeInfo {
        node_count: 3,
        variable_count: 2,
    };
    assert_eq!(a, b);
}

#[test]
fn test_three_var_full_verification() {
    // A = {(x1), (NOT x1, x2)}, B = {(NOT x2, x3), (NOT x3)}.
    // A forces x2=T. Shared: {x2}. I = x2 is valid.
    let a = vec![vec![1], vec![-1, 2]];
    let b = vec![vec![-2, 3], vec![-3]];
    assert!(verify_all_properties(&a, &b, &var(2), 3).all_valid);
}

#[test]
fn test_three_var_wrong_interpolant() {
    let a = vec![vec![1], vec![-1, 2]];
    let b = vec![vec![-2, 3], vec![-3]];
    let result = verify_all_properties(&a, &b, &not(var(2)), 3);
    assert!(!result.implication_holds);
    assert!(!result.all_valid);
}
