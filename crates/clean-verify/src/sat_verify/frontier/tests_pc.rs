// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Polynomial Calculus over GF(2).

use std::collections::HashMap;

use super::polynomial_calculus::*;

// ---------------------------------------------------------------------------
// GF(2) arithmetic basics
// ---------------------------------------------------------------------------

#[test]
fn test_gf2_zero_and_one() {
    let zero = GF2Polynomial::zero();
    let one = GF2Polynomial::one();

    assert!(zero.is_zero());
    assert!(!zero.is_one());
    assert!(one.is_one());
    assert!(!one.is_zero());
}

#[test]
fn test_gf2_addition_xor() {
    // 1 + 1 = 0 in GF(2).
    let one = GF2Polynomial::one();
    let sum = one.add(&one);
    assert!(sum.is_zero(), "1 + 1 should be 0 in GF(2)");
}

#[test]
fn test_gf2_addition_identity() {
    // 0 + p = p.
    let x = GF2Polynomial::var(0);
    let sum = GF2Polynomial::zero().add(&x);
    assert_eq!(sum, x);
}

#[test]
fn test_gf2_x_squared_equals_x() {
    // x^2 = x in GF(2) (idempotency / field equation).
    let x = GF2Polynomial::var(0);
    let x_sq = x.mul(&x);
    assert_eq!(x_sq, x, "x^2 should equal x in GF(2)");
}

#[test]
fn test_gf2_multiplication_distributes() {
    // x * (x + 1) = x^2 + x = x + x = 0 in GF(2).
    let x = GF2Polynomial::var(0);
    let one = GF2Polynomial::one();
    let x_plus_1 = x.add(&one);
    let product = x.mul(&x_plus_1);
    assert!(
        product.is_zero(),
        "x * (1 + x) should be 0 in GF(2), got {} terms",
        product.num_terms()
    );
}

#[test]
fn test_gf2_degree() {
    let zero = GF2Polynomial::zero();
    let one = GF2Polynomial::one();
    let x = GF2Polynomial::var(0);
    let xy = GF2Polynomial::monomial(&[0, 1]);

    assert_eq!(zero.degree(), 0);
    assert_eq!(one.degree(), 0);
    assert_eq!(x.degree(), 1);
    assert_eq!(xy.degree(), 2);
}

#[test]
fn test_gf2_evaluate() {
    // p(x, y) = x*y + x + 1
    let xy = GF2Polynomial::monomial(&[0, 1]);
    let x = GF2Polynomial::var(0);
    let one = GF2Polynomial::one();
    let p = xy.add(&x).add(&one);

    // p(0, 0) = 0 + 0 + 1 = 1
    let mut assign = HashMap::new();
    assign.insert(0, false);
    assign.insert(1, false);
    assert!(p.evaluate(&assign));

    // p(1, 0) = 0 + 1 + 1 = 0
    assign.insert(0, true);
    assign.insert(1, false);
    assert!(!p.evaluate(&assign));

    // p(1, 1) = 1 + 1 + 1 = 1
    assign.insert(0, true);
    assign.insert(1, true);
    assert!(p.evaluate(&assign));
}

// ---------------------------------------------------------------------------
// Clause encoding
// ---------------------------------------------------------------------------

#[test]
fn test_clause_encoding_single_positive() {
    // Clause (x1) encodes as (1 - x0) = 0, i.e., polynomial = 1 + x0.
    // DIMACS var 1 -> polynomial var 0.
    let p = clause_to_polynomial(&[1]);
    let one = GF2Polynomial::one();
    let x0 = GF2Polynomial::var(0);
    let expected = one.add(&x0); // 1 + x0
    assert_eq!(p, expected);
}

#[test]
fn test_clause_encoding_single_negative() {
    // Clause (-x1) encodes as x0 = 0, i.e., polynomial = x0.
    let p = clause_to_polynomial(&[-1]);
    assert_eq!(p, GF2Polynomial::var(0));
}

#[test]
fn test_clause_encoding_x_and_not_x() {
    // Encode (x) AND (-x) as two polynomials.
    // (x): 1 + x0 = 0
    // (-x): x0 = 0
    // Sum: (1 + x0) + x0 = 1 = 0, which is the contradiction.
    let p1 = clause_to_polynomial(&[1]);
    let p2 = clause_to_polynomial(&[-1]);
    let sum = p1.add(&p2);
    assert!(sum.is_one(), "x + NOT x should yield constant 1");
}

// ---------------------------------------------------------------------------
// PC proof verification (S44)
// ---------------------------------------------------------------------------

#[test]
fn test_pc_proof_x_and_not_x() {
    // Formula: (x) AND (NOT x) -- UNSAT.
    // Axiom 0: 1 + x0    (clause (x))
    // Axiom 1: x0         (clause (-x))
    // Step 0: Axiom(0)    -> 1 + x0
    // Step 1: Axiom(1)    -> x0
    // Step 2: Add(0, 1)   -> (1 + x0) + x0 = 1
    let axioms = vec![clause_to_polynomial(&[1]), clause_to_polynomial(&[-1])];

    let steps = vec![PCStep::Axiom(0), PCStep::Axiom(1), PCStep::Add(0, 1)];

    assert!(verify_pc_proof(&axioms, &steps));
}

#[test]
fn test_pc_proof_invalid_no_contradiction() {
    // Just introduce an axiom, never derive 1.
    let axioms = vec![clause_to_polynomial(&[1])];
    let steps = vec![PCStep::Axiom(0)];
    assert!(!verify_pc_proof(&axioms, &steps));
}

#[test]
fn test_pc_proof_invalid_index() {
    let axioms = vec![clause_to_polynomial(&[1])];
    let steps = vec![PCStep::Axiom(5)]; // Out of bounds.
    assert!(!verify_pc_proof(&axioms, &steps));
}

#[test]
fn test_pc_proof_multiply_then_add() {
    // Axiom 0: x0           (clause (-x1))
    // Axiom 1: 1 + x0       (clause (x1))
    // Step 0: Axiom(0)      -> x0
    // Step 1: Multiply(0, 0) -> x0 * x0 = x0  (idempotent)
    // Step 2: Axiom(1)      -> 1 + x0
    // Step 3: Add(1, 2)     -> x0 + (1 + x0) = 1
    let axioms = vec![clause_to_polynomial(&[-1]), clause_to_polynomial(&[1])];

    let steps = vec![
        PCStep::Axiom(0),
        PCStep::Multiply(0, 0),
        PCStep::Axiom(1),
        PCStep::Add(1, 2),
    ];

    assert!(verify_pc_proof(&axioms, &steps));
}

// ---------------------------------------------------------------------------
// PHP(2,1): Pigeonhole Principle -- 2 pigeons, 1 hole
// ---------------------------------------------------------------------------

#[test]
fn test_pc_proof_php_2_1() {
    // PHP(2,1): 2 pigeons must go into 1 hole -- impossible.
    //
    // Variables:
    //   x_{p,h} = pigeon p goes to hole h (only h=1 here).
    //   x_{1,1} = DIMACS var 1 -> poly var 0
    //   x_{2,1} = DIMACS var 2 -> poly var 1
    //
    // Axioms from PHP:
    //   Pigeon 1 must go somewhere: (x_{1,1}) -> poly: 1 + x0
    //   Pigeon 2 must go somewhere: (x_{2,1}) -> poly: 1 + x1
    //   Hole 1 has at most one pigeon: (-x_{1,1} OR -x_{2,1}) -> poly: x0 * x1
    //
    // PC refutation:
    //   Step 0: Axiom(0)  -> 1 + x0
    //   Step 1: Axiom(1)  -> 1 + x1
    //   Step 2: Axiom(2)  -> x0 * x1
    //   Step 3: Multiply(0, 1) -> (1 + x0) * x1 = x1 + x0*x1
    //   Step 4: Add(2, 3)      -> x0*x1 + x1 + x0*x1 = x1
    //   Step 5: Add(1, 4)      -> (1 + x1) + x1 = 1  -- contradiction!
    let axioms = vec![
        clause_to_polynomial(&[1]),      // pigeon 1 -> hole 1
        clause_to_polynomial(&[2]),      // pigeon 2 -> hole 1
        clause_to_polynomial(&[-1, -2]), // at most one pigeon per hole
    ];

    let steps = vec![
        PCStep::Axiom(0),       // 0: 1 + x0
        PCStep::Axiom(1),       // 1: 1 + x1
        PCStep::Axiom(2),       // 2: x0*x1
        PCStep::Multiply(0, 1), // 3: (1+x0)*x1 = x1 + x0*x1
        PCStep::Add(2, 3),      // 4: x0*x1 + (x1 + x0*x1) = x1
        PCStep::Add(1, 4),      // 5: (1+x1) + x1 = 1
    ];

    assert!(
        verify_pc_proof(&axioms, &steps),
        "PHP(2,1) should have a valid PC/GF(2) refutation"
    );
}

// ---------------------------------------------------------------------------
// Proof degree measurement
// ---------------------------------------------------------------------------

#[test]
fn test_proof_degree_php_2_1() {
    let axioms = vec![
        clause_to_polynomial(&[1]),
        clause_to_polynomial(&[2]),
        clause_to_polynomial(&[-1, -2]),
    ];

    let steps = vec![
        PCStep::Axiom(0),
        PCStep::Axiom(1),
        PCStep::Axiom(2),
        PCStep::Multiply(0, 1),
        PCStep::Add(2, 3),
        PCStep::Add(1, 4),
    ];

    let deg = proof_degree(&axioms, &steps);
    // The at-most-one axiom is degree 2, and the multiply step
    // produces degree 2, so max degree should be 2.
    assert_eq!(deg, 2);
}

#[test]
fn test_proof_degree_linear() {
    // Simple x AND NOT x proof -- max degree 1.
    let axioms = vec![clause_to_polynomial(&[1]), clause_to_polynomial(&[-1])];
    let steps = vec![PCStep::Axiom(0), PCStep::Axiom(1), PCStep::Add(0, 1)];

    let deg = proof_degree(&axioms, &steps);
    assert_eq!(deg, 1);
}

// ---------------------------------------------------------------------------
// Weaken step
// ---------------------------------------------------------------------------

#[test]
fn test_pc_weaken_step() {
    // Start with 0 polynomial, weaken by adding monomial {}, which is 1.
    // Axiom 0: x0         (clause (-x1))
    // Axiom 1: 1 + x0     (clause (x1))
    // Step 0: Axiom(0)   -> x0
    // Step 1: Axiom(1)   -> 1 + x0
    // Step 2: Add(0, 1)  -> 1
    let axioms = vec![clause_to_polynomial(&[-1]), clause_to_polynomial(&[1])];
    let steps = vec![PCStep::Axiom(0), PCStep::Axiom(1), PCStep::Add(0, 1)];
    assert!(verify_pc_proof(&axioms, &steps));
}
