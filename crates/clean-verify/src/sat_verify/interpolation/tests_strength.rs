// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for interpolation strength metrics and comparison.

use super::strength::{
    compare_interpolants, interpolant_depth, interpolant_size, interpolant_variables,
    is_stronger_interpolant, simplify_interpolant, InterpolantComparison, I09_INTERPOLANT_STRENGTH,
};
use super::PropFormula;
use crate::spec::ProofStatus;

// ---- Helper constructors ----

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

fn implies(l: PropFormula, r: PropFormula) -> PropFormula {
    PropFormula::Implies(Box::new(l), Box::new(r))
}

// ---- Size tests ----

#[test]
fn test_size_atom() {
    assert_eq!(interpolant_size(&var(1)), 1);
    assert_eq!(interpolant_size(&PropFormula::True), 1);
    assert_eq!(interpolant_size(&PropFormula::False), 1);
}

#[test]
fn test_size_negation() {
    assert_eq!(interpolant_size(&not(var(1))), 2);
}

#[test]
fn test_size_binary() {
    // AND(var(1), var(2)) = 3 nodes
    assert_eq!(interpolant_size(&and(var(1), var(2))), 3);
}

#[test]
fn test_size_nested() {
    // AND(OR(var(1), var(2)), NOT(var(3))) = 1 + (1 + 1 + 1) + (1 + 1) = 6
    let f = and(or(var(1), var(2)), not(var(3)));
    assert_eq!(interpolant_size(&f), 6);
}

#[test]
fn test_size_complex() {
    // IMPLIES(AND(var(1), var(2)), OR(var(3), NOT(var(4))))
    // = 1 + (1 + 1 + 1) + (1 + (1 + 1)) = 7
    let f = implies(and(var(1), var(2)), or(var(3), not(var(4))));
    assert_eq!(interpolant_size(&f), 8);
}

// ---- Depth tests ----

#[test]
fn test_depth_atom() {
    assert_eq!(interpolant_depth(&var(1)), 0);
    assert_eq!(interpolant_depth(&PropFormula::True), 0);
    assert_eq!(interpolant_depth(&PropFormula::False), 0);
}

#[test]
fn test_depth_flat() {
    // AND(var(1), var(2)) = depth 1
    assert_eq!(interpolant_depth(&and(var(1), var(2))), 1);
}

#[test]
fn test_depth_deep() {
    // NOT(NOT(NOT(var(1)))) = depth 3
    assert_eq!(interpolant_depth(&not(not(not(var(1))))), 3);
}

#[test]
fn test_depth_asymmetric() {
    // OR(var(1), AND(var(2), NOT(var(3)))) = depth 1 + max(0, 1 + max(0, 1)) = 3
    let f = or(var(1), and(var(2), not(var(3))));
    assert_eq!(interpolant_depth(&f), 3);
}

#[test]
fn test_depth_implies() {
    assert_eq!(interpolant_depth(&implies(var(1), var(2))), 1);
}

// ---- Variables tests ----

#[test]
fn test_variables_none() {
    assert!(interpolant_variables(&PropFormula::True).is_empty());
    assert!(interpolant_variables(&PropFormula::False).is_empty());
}

#[test]
fn test_variables_single() {
    assert_eq!(interpolant_variables(&var(5)), vec![5]);
}

#[test]
fn test_variables_many() {
    let f = and(or(var(3), var(1)), not(var(7)));
    assert_eq!(interpolant_variables(&f), vec![1, 3, 7]);
}

#[test]
fn test_variables_deduped() {
    // var(1) appears twice
    let f = and(var(1), or(var(1), var(2)));
    assert_eq!(interpolant_variables(&f), vec![1, 2]);
}

#[test]
fn test_variables_sorted() {
    let f = or(var(10), and(var(2), var(5)));
    let vars = interpolant_variables(&f);
    let mut sorted = vars.clone();
    sorted.sort();
    assert_eq!(vars, sorted);
}

// ---- Comparison tests ----

#[test]
fn test_compare_equal() {
    let f = var(1);
    let cmp = compare_interpolants(&f, &f);
    assert!((cmp.size_ratio - 1.0).abs() < f64::EPSILON);
    assert!((cmp.depth_ratio - 1.0).abs() < f64::EPSILON);
    assert!((cmp.var_count_ratio - 1.0).abs() < f64::EPSILON);
    assert!(!cmp.is_simpler); // not strictly smaller
}

#[test]
fn test_compare_smaller() {
    let small = var(1);
    let large = and(var(1), or(var(2), var(3)));
    let cmp = compare_interpolants(&small, &large);
    assert!(cmp.size_ratio < 1.0);
    assert!(cmp.is_simpler);
}

#[test]
fn test_compare_larger() {
    let small = var(1);
    let large = and(var(1), var(2));
    let cmp = compare_interpolants(&large, &small);
    assert!(cmp.size_ratio > 1.0);
    assert!(!cmp.is_simpler);
}

#[test]
fn test_compare_different_depths() {
    let shallow = and(var(1), var(2)); // depth 1
    let deep = and(var(1), not(not(var(2)))); // depth 3
    let cmp = compare_interpolants(&shallow, &deep);
    assert!(cmp.depth_ratio < 1.0);
}

// ---- Strength tests ----

#[test]
fn test_stronger_tautology_implies_everything() {
    // True implies any formula
    let candidate = PropFormula::False; // False has 0 models -> strongest possible
    let reference = var(1);
    assert!(is_stronger_interpolant(&candidate, &reference, &[1]));
}

#[test]
fn test_stronger_contradiction_is_strongest() {
    // False implies everything (vacuously)
    let candidate = PropFormula::False;
    let reference = PropFormula::True;
    assert!(is_stronger_interpolant(&candidate, &reference, &[1]));
}

#[test]
fn test_stronger_true_is_weakest() {
    // True does not imply var(1) (True is true when var(1) is false)
    assert!(!is_stronger_interpolant(&PropFormula::True, &var(1), &[1]));
}

#[test]
fn test_stronger_self_implies_self() {
    let f = and(var(1), var(2));
    assert!(is_stronger_interpolant(&f, &f, &[1, 2]));
}

#[test]
fn test_stronger_conjunction_implies_disjuncts() {
    // (A AND B) implies A
    let conj = and(var(1), var(2));
    assert!(is_stronger_interpolant(&conj, &var(1), &[1, 2]));
    assert!(is_stronger_interpolant(&conj, &var(2), &[1, 2]));
}

#[test]
fn test_stronger_disjunct_does_not_imply_conjunction() {
    // A does not imply (A AND B)
    assert!(!is_stronger_interpolant(
        &var(1),
        &and(var(1), var(2)),
        &[1, 2]
    ));
}

#[test]
fn test_stronger_empty_shared_vars() {
    // With no shared vars, there's exactly one assignment (the empty one).
    // Both True and True evaluate to true, so True implies True.
    assert!(is_stronger_interpolant(
        &PropFormula::True,
        &PropFormula::True,
        &[]
    ));
}

// ---- Simplification tests ----

#[test]
fn test_simplify_double_negation() {
    let f = not(not(var(1)));
    assert_eq!(simplify_interpolant(&f), var(1));
}

#[test]
fn test_simplify_triple_negation() {
    let f = not(not(not(var(1))));
    assert_eq!(simplify_interpolant(&f), not(var(1)));
}

#[test]
fn test_simplify_and_identity() {
    assert_eq!(
        simplify_interpolant(&and(var(1), PropFormula::True)),
        var(1)
    );
    assert_eq!(
        simplify_interpolant(&and(PropFormula::True, var(2))),
        var(2)
    );
}

#[test]
fn test_simplify_and_annihilation() {
    assert_eq!(
        simplify_interpolant(&and(var(1), PropFormula::False)),
        PropFormula::False
    );
    assert_eq!(
        simplify_interpolant(&and(PropFormula::False, var(2))),
        PropFormula::False
    );
}

#[test]
fn test_simplify_or_identity() {
    assert_eq!(
        simplify_interpolant(&or(var(1), PropFormula::False)),
        var(1)
    );
    assert_eq!(
        simplify_interpolant(&or(PropFormula::False, var(2))),
        var(2)
    );
}

#[test]
fn test_simplify_or_annihilation() {
    assert_eq!(
        simplify_interpolant(&or(var(1), PropFormula::True)),
        PropFormula::True
    );
}

#[test]
fn test_simplify_implies_false_antecedent() {
    assert_eq!(
        simplify_interpolant(&implies(PropFormula::False, var(1))),
        PropFormula::True
    );
}

#[test]
fn test_simplify_implies_true_antecedent() {
    assert_eq!(
        simplify_interpolant(&implies(PropFormula::True, var(1))),
        var(1)
    );
}

#[test]
fn test_simplify_implies_true_consequent() {
    assert_eq!(
        simplify_interpolant(&implies(var(1), PropFormula::True)),
        PropFormula::True
    );
}

#[test]
fn test_simplify_absorption_and() {
    // p AND p -> p
    assert_eq!(simplify_interpolant(&and(var(1), var(1))), var(1));
}

#[test]
fn test_simplify_absorption_or() {
    // p OR p -> p
    assert_eq!(simplify_interpolant(&or(var(1), var(1))), var(1));
}

#[test]
fn test_simplify_complementation_and() {
    // p AND (NOT p) -> False
    assert_eq!(
        simplify_interpolant(&and(var(1), not(var(1)))),
        PropFormula::False
    );
}

#[test]
fn test_simplify_complementation_or() {
    // p OR (NOT p) -> True
    assert_eq!(
        simplify_interpolant(&or(var(1), not(var(1)))),
        PropFormula::True
    );
}

#[test]
fn test_simplify_implies_self() {
    // p -> p = True
    assert_eq!(
        simplify_interpolant(&implies(var(1), var(1))),
        PropFormula::True
    );
}

#[test]
fn test_simplify_complex_nested() {
    // NOT(NOT(AND(var(1), True))) -> var(1)
    let f = not(not(and(var(1), PropFormula::True)));
    assert_eq!(simplify_interpolant(&f), var(1));
}

#[test]
fn test_simplify_preserves_irreducible() {
    // AND(var(1), var(2)) is already simplified
    let f = and(var(1), var(2));
    assert_eq!(simplify_interpolant(&f), and(var(1), var(2)));
}

// ---- Edge cases ----

#[test]
fn test_size_constants() {
    assert_eq!(interpolant_size(&PropFormula::True), 1);
    assert_eq!(interpolant_size(&PropFormula::False), 1);
}

#[test]
fn test_depth_constants() {
    assert_eq!(interpolant_depth(&PropFormula::True), 0);
    assert_eq!(interpolant_depth(&PropFormula::False), 0);
}

#[test]
fn test_proof_status_constant() {
    assert_eq!(I09_INTERPOLANT_STRENGTH, ProofStatus::DerivedPending);
}

#[test]
fn test_simplify_negation_of_true() {
    assert_eq!(
        simplify_interpolant(&not(PropFormula::True)),
        PropFormula::False
    );
}

#[test]
fn test_simplify_negation_of_false() {
    assert_eq!(
        simplify_interpolant(&not(PropFormula::False)),
        PropFormula::True
    );
}

#[test]
fn test_compare_both_constants() {
    let cmp = compare_interpolants(&PropFormula::True, &PropFormula::False);
    assert!((cmp.size_ratio - 1.0).abs() < f64::EPSILON);
    assert!((cmp.depth_ratio - 1.0).abs() < f64::EPSILON);
}

#[test]
fn test_variables_implies_collects_both_sides() {
    let f = implies(var(1), var(2));
    assert_eq!(interpolant_variables(&f), vec![1, 2]);
}
