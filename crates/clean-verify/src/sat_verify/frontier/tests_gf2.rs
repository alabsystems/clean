// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Additional tests for GF(2) Polynomial Calculus (S44).
//!
//! Focused on the x^2 = x reduction property, multilinear invariant
//! preservation, and edge cases in the proof system. Complements the
//! core tests in `tests_pc.rs`.

use std::collections::HashMap;

use super::polynomial_calculus::*;

// =========================================================================
// x^2 = x reduction -- the core GF(2) property
// =========================================================================

#[test]
fn test_gf2_x_cubed_equals_x() {
    // x^3 = x * x * x = x * x = x in GF(2).
    let x = GF2Polynomial::var(0);
    let x_cubed = x.mul(&x).mul(&x);
    assert_eq!(x_cubed, x, "x^3 should equal x in GF(2)");
}

#[test]
fn test_gf2_x_fourth_equals_x() {
    let x = GF2Polynomial::var(0);
    let x4 = x.mul(&x).mul(&x).mul(&x);
    assert_eq!(x4, x, "x^4 should equal x in GF(2)");
}

#[test]
fn test_gf2_xy_squared_equals_xy() {
    // (x*y)^2 = x*y in multilinear: x*y * x*y = x^2*y^2 = x*y
    let xy = GF2Polynomial::monomial(&[0, 1]);
    let xy_sq = xy.mul(&xy);
    assert_eq!(xy_sq, xy, "(x*y)^2 = x*y in GF(2)");
}

#[test]
fn test_gf2_multilinear_reduction_three_vars() {
    // x * y * z * x = x * y * z (x^2 = x in union)
    let xyz = GF2Polynomial::monomial(&[0, 1, 2]);
    let x = GF2Polynomial::var(0);
    let prod = xyz.mul(&x);
    assert_eq!(prod, xyz, "x*y*z * x = x*y*z in GF(2)");
}

#[test]
fn test_gf2_reduction_all_single_vars() {
    for i in 0..5 {
        let x = GF2Polynomial::var(i);
        let x_sq = x.mul(&x);
        assert_eq!(x_sq, x, "x{i}^2 should equal x{i}");
    }
}

// =========================================================================
// Algebraic identities in GF(2)
// =========================================================================

#[test]
fn test_gf2_x_times_one_minus_x_is_zero() {
    // x * (1 + x) = x + x^2 = x + x = 0 in GF(2)
    let x = GF2Polynomial::var(0);
    let one = GF2Polynomial::one();
    let one_plus_x = one.add(&x);
    let product = x.mul(&one_plus_x);
    assert!(product.is_zero(), "x * (1-x) = 0 in GF(2)");
}

#[test]
fn test_gf2_de_morgan_and_or() {
    // In GF(2): AND(x,y) = x*y, OR(x,y) = x + y + x*y
    // Verify: NOT OR(x,y) = 1 + x + y + x*y
    //         AND(NOT x, NOT y) = (1+x)(1+y) = 1 + x + y + x*y
    let x = GF2Polynomial::var(0);
    let y = GF2Polynomial::var(1);
    let one = GF2Polynomial::one();

    let not_x = one.add(&x);
    let not_y = one.add(&y);
    let and_nots = not_x.mul(&not_y);

    let or_xy = x.add(&y).add(&x.mul(&y));
    let not_or = one.add(&or_xy);

    assert_eq!(and_nots, not_or, "De Morgan: NOT(x OR y) = NOT x AND NOT y");
}

#[test]
fn test_gf2_associativity_addition() {
    let a = GF2Polynomial::var(0);
    let b = GF2Polynomial::var(1);
    let c = GF2Polynomial::var(2);
    assert_eq!(a.add(&b).add(&c), a.add(&b.add(&c)));
}

#[test]
fn test_gf2_commutativity_multiply() {
    let xy = GF2Polynomial::var(0).mul(&GF2Polynomial::var(1));
    let yx = GF2Polynomial::var(1).mul(&GF2Polynomial::var(0));
    assert_eq!(xy, yx);
}

#[test]
fn test_gf2_distribution_over_three_terms() {
    // z * (x + y + 1) = z*x + z*y + z
    let x = GF2Polynomial::var(0);
    let y = GF2Polynomial::var(1);
    let z = GF2Polynomial::var(2);
    let one = GF2Polynomial::one();

    let sum = x.add(&y).add(&one);
    let distributed = z.mul(&sum);

    let manual = z.mul(&x).add(&z.mul(&y)).add(&z);
    assert_eq!(distributed, manual);
}

// =========================================================================
// Clause encoding edge cases
// =========================================================================

#[test]
fn test_encode_three_literal_clause() {
    // (x1 OR x2 OR x3): all false when x1=0, x2=0, x3=0
    // factors: (1-x0)(1-x1)(1-x2)
    let p = clause_to_polynomial(&[1, 2, 3]);
    // expand: 1 + x0 + x1 + x2 + x0x1 + x0x2 + x1x2 + x0x1x2
    assert_eq!(p.num_terms(), 8);
}

#[test]
fn test_encode_all_negative_clause() {
    // (NOT x1 OR NOT x2): factors x0 * x1
    let p = clause_to_polynomial(&[-1, -2]);
    assert_eq!(p, GF2Polynomial::monomial(&[0, 1]));
}

#[test]
fn test_clause_polynomial_evaluates_correctly() {
    // (x1 OR x2): polynomial should be 1 only when x1=0 AND x2=0
    let p = clause_to_polynomial(&[1, 2]);
    let mut assign = HashMap::new();

    // x1=0, x2=0: clause violated, polynomial = 1
    assign.insert(0, false);
    assign.insert(1, false);
    assert!(p.evaluate(&assign), "clause violated when both false");

    // x1=1, x2=0: clause satisfied, polynomial = 0
    assign.insert(0, true);
    assign.insert(1, false);
    assert!(!p.evaluate(&assign), "clause satisfied when x1 true");

    // x1=1, x2=1: clause satisfied
    assign.insert(0, true);
    assign.insert(1, true);
    assert!(!p.evaluate(&assign));
}

// =========================================================================
// Proof verification edge cases
// =========================================================================

#[test]
fn test_empty_proof_is_invalid() {
    let axioms = vec![clause_to_polynomial(&[1])];
    assert!(!verify_pc_proof(&axioms, &[]));
}

#[test]
fn test_proof_single_axiom_not_one_is_invalid() {
    let axioms = vec![GF2Polynomial::var(0)];
    let steps = vec![PCStep::Axiom(0)];
    assert!(!verify_pc_proof(&axioms, &steps));
}

#[test]
fn test_proof_degree_empty_axioms() {
    let deg = proof_degree(&[], &[]);
    assert_eq!(deg, 0);
}

#[test]
fn test_weaken_to_derive_one() {
    // Start from zero polynomial (boolean axiom gives 0), weaken by adding 1
    // This isn't actually sound PC, but tests the weaken step mechanics
    // Step 0: Axiom(0) -> x0
    // Step 1: Axiom(1) -> 1 + x0
    // Step 2: Add(0, 1) -> 1
    let axioms = vec![clause_to_polynomial(&[-1]), clause_to_polynomial(&[1])];
    let steps = vec![PCStep::Axiom(0), PCStep::Axiom(1), PCStep::Add(0, 1)];
    assert!(verify_pc_proof(&axioms, &steps));
}
