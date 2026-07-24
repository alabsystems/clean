// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the enhanced GF(2) polynomial algebra, tracked PC proofs,
//! CNF encoding bridge, soundness theorem (ZT03), and competition
//! certificate compilation (partial ZT04).

use super::gf2_algebra::*;

// =========================================================================
// Gf2Poly arithmetic
// =========================================================================

#[test]
fn test_gf2poly_zero_one() {
    let zero = Gf2Poly::zero();
    let one = Gf2Poly::one();
    assert!(zero.is_zero());
    assert!(!zero.is_one());
    assert!(one.is_one());
    assert!(!one.is_zero());
}

#[test]
fn test_gf2poly_add_xor() {
    let one = Gf2Poly::one();
    let sum = one.add(&one);
    assert!(sum.is_zero(), "1 + 1 = 0 in GF(2)");
}

#[test]
fn test_gf2poly_add_identity() {
    let x = Gf2Poly::variable(0);
    let sum = Gf2Poly::zero().add(&x);
    assert_eq!(sum, x);
}

#[test]
fn test_gf2poly_x_squared_equals_x() {
    let x = Gf2Poly::variable(0);
    let x_sq = x.mul(&x);
    assert_eq!(x_sq, x, "x^2 = x in GF(2)");
}

#[test]
fn test_gf2poly_x_cubed_equals_x() {
    let x = Gf2Poly::variable(0);
    let x3 = x.mul(&x).mul(&x);
    assert_eq!(x3, x, "x^3 = x in GF(2)");
}

#[test]
fn test_gf2poly_xy_squared_equals_xy() {
    let xy = Gf2Poly::monomial(&[0, 1]);
    let xy_sq = xy.mul(&xy);
    assert_eq!(xy_sq, xy, "(xy)^2 = xy in GF(2)");
}

#[test]
fn test_gf2poly_mul_distributes() {
    // x * (1 + x) = x + x^2 = x + x = 0 in GF(2)
    let x = Gf2Poly::variable(0);
    let one = Gf2Poly::one();
    let one_plus_x = one.add(&x);
    let product = x.mul(&one_plus_x);
    assert!(product.is_zero(), "x * (1+x) = 0 in GF(2)");
}

#[test]
fn test_gf2poly_degree() {
    assert_eq!(Gf2Poly::zero().degree(), 0);
    assert_eq!(Gf2Poly::one().degree(), 0);
    assert_eq!(Gf2Poly::variable(0).degree(), 1);
    assert_eq!(Gf2Poly::monomial(&[0, 1]).degree(), 2);
    assert_eq!(Gf2Poly::monomial(&[0, 1, 2]).degree(), 3);
}

#[test]
fn test_gf2poly_num_terms() {
    assert_eq!(Gf2Poly::zero().num_terms(), 0);
    assert_eq!(Gf2Poly::one().num_terms(), 1);
    assert_eq!(Gf2Poly::variable(0).num_terms(), 1);
    // 1 + x + y + xy has 4 terms
    let p = Gf2Poly::from_clause(&[1, 2]);
    assert_eq!(p.num_terms(), 4);
}

#[test]
fn test_gf2poly_evaluate() {
    // p = x0*x1 + x0 + 1
    let xy = Gf2Poly::monomial(&[0, 1]);
    let x = Gf2Poly::variable(0);
    let one = Gf2Poly::one();
    let p = xy.add(&x).add(&one);

    // p(0,0) = 0 + 0 + 1 = 1
    assert!(p.evaluate(&[false, false]));
    // p(1,0) = 0 + 1 + 1 = 0
    assert!(!p.evaluate(&[true, false]));
    // p(1,1) = 1 + 1 + 1 = 1
    assert!(p.evaluate(&[true, true]));
    // p(0,1) = 0 + 0 + 1 = 1
    assert!(p.evaluate(&[false, true]));
}

#[test]
fn test_gf2poly_commutativity() {
    let x = Gf2Poly::variable(0);
    let y = Gf2Poly::variable(1);
    assert_eq!(x.mul(&y), y.mul(&x));
    assert_eq!(x.add(&y), y.add(&x));
}

#[test]
fn test_gf2poly_associativity() {
    let a = Gf2Poly::variable(0);
    let b = Gf2Poly::variable(1);
    let c = Gf2Poly::variable(2);
    assert_eq!(a.add(&b).add(&c), a.add(&b.add(&c)));
    assert_eq!(a.mul(&b).mul(&c), a.mul(&b.mul(&c)));
}

#[test]
fn test_gf2poly_de_morgan() {
    let x = Gf2Poly::variable(0);
    let y = Gf2Poly::variable(1);
    let one = Gf2Poly::one();

    let not_x = one.add(&x);
    let not_y = one.add(&y);
    let and_nots = not_x.mul(&not_y);

    let or_xy = x.add(&y).add(&x.mul(&y));
    let not_or = one.add(&or_xy);

    assert_eq!(and_nots, not_or, "De Morgan: NOT(OR) = AND(NOT,NOT)");
}

// =========================================================================
// Boolean axiom
// =========================================================================

#[test]
fn test_gf2poly_boolean_axiom_is_zero() {
    for v in 0..5 {
        let ax = Gf2Poly::boolean_axiom(v);
        assert!(ax.is_zero(), "boolean axiom x^2 + x = 0 for var {v}");
    }
}

// =========================================================================
// Clause encoding
// =========================================================================

#[test]
fn test_gf2poly_from_clause_positive() {
    // (x1): 1 - x0 = 1 + x0 in GF(2)
    let p = Gf2Poly::from_clause(&[1]);
    let expected = Gf2Poly::one().add(&Gf2Poly::variable(0));
    assert_eq!(p, expected);
}

#[test]
fn test_gf2poly_from_clause_negative() {
    // (-x1): x0
    let p = Gf2Poly::from_clause(&[-1]);
    assert_eq!(p, Gf2Poly::variable(0));
}

#[test]
fn test_gf2poly_from_clause_two_literals() {
    // (x1 v x2): (1-x0)(1-x1) = 1 + x0 + x1 + x0*x1
    let p = Gf2Poly::from_clause(&[1, 2]);
    assert_eq!(p.num_terms(), 4);
    assert_eq!(p.degree(), 2);
}

#[test]
fn test_gf2poly_from_clause_all_negative() {
    // (-x1 v -x2): x0 * x1
    let p = Gf2Poly::from_clause(&[-1, -2]);
    assert_eq!(p, Gf2Poly::monomial(&[0, 1]));
}

#[test]
fn test_gf2poly_clause_evaluation() {
    // (x1 v x2): poly=1 when clause violated (both false)
    let p = Gf2Poly::from_clause(&[1, 2]);
    assert!(p.evaluate(&[false, false]), "clause violated");
    assert!(!p.evaluate(&[true, false]), "clause satisfied by x1");
    assert!(!p.evaluate(&[false, true]), "clause satisfied by x2");
    assert!(!p.evaluate(&[true, true]), "clause satisfied by both");
}

#[test]
fn test_gf2poly_to_clause_roundtrip() {
    let clauses = vec![vec![1], vec![-1], vec![1, 2], vec![-1, -2], vec![1, -2, 3]];
    for clause in &clauses {
        let p = Gf2Poly::from_clause(clause);
        let recovered = p.to_clause();
        assert!(recovered.is_some(), "should recover clause {clause:?}");
        let recovered = recovered.expect("tested above");
        // The recovered clause may differ in order/sign assignment but
        // must produce the same polynomial.
        let p2 = Gf2Poly::from_clause(&recovered);
        assert_eq!(p, p2, "roundtrip for clause {clause:?}");
    }
}

// =========================================================================
// CNF <-> GF(2) encoding bridge
// =========================================================================

#[test]
fn test_cnf_to_gf2_system_basic() {
    let clauses = vec![vec![1], vec![-1]];
    let polys = cnf_to_gf2_system(&clauses);
    assert_eq!(polys.len(), 2);
    assert_eq!(polys[0], Gf2Poly::from_clause(&[1]));
    assert_eq!(polys[1], Gf2Poly::from_clause(&[-1]));
}

#[test]
fn test_verify_encoding_soundness_unit_clauses() {
    let clauses = vec![vec![1], vec![-1]];
    let polys = cnf_to_gf2_system(&clauses);
    assert!(verify_encoding_soundness(&clauses, &polys, 1));
}

#[test]
fn test_verify_encoding_soundness_php_2_1() {
    let clauses = vec![vec![1], vec![2], vec![-1, -2]];
    let polys = cnf_to_gf2_system(&clauses);
    assert!(verify_encoding_soundness(&clauses, &polys, 2));
}

#[test]
fn test_verify_encoding_soundness_sat_instance() {
    // (x1 v x2) -- satisfiable
    let clauses = vec![vec![1, 2]];
    let polys = cnf_to_gf2_system(&clauses);
    assert!(verify_encoding_soundness(&clauses, &polys, 2));
}

#[test]
fn test_verify_encoding_soundness_mismatched_polys() {
    let clauses = vec![vec![1]];
    let wrong_polys = vec![Gf2Poly::variable(1)]; // wrong encoding
    assert!(!verify_encoding_soundness(&clauses, &wrong_polys, 2));
}

#[test]
fn test_verify_encoding_soundness_too_many_vars() {
    let clauses = vec![vec![1]];
    let polys = cnf_to_gf2_system(&clauses);
    // num_vars > 20 returns false conservatively.
    assert!(!verify_encoding_soundness(&clauses, &polys, 21));
}

// =========================================================================
// PC proof construction and verification
// =========================================================================

#[test]
fn test_pc_proof_x_and_not_x() {
    // {x} AND {-x}: UNSAT
    let clauses = vec![vec![1], vec![-1]];
    let steps = vec![
        PcStepTracked::ClauseAxiom(0), // 1 + x0
        PcStepTracked::ClauseAxiom(1), // x0
        PcStepTracked::Add(0, 1),      // 1
    ];
    let proof = PcProof::build(&clauses, steps).expect("should build");
    proof.verify().expect("should derive 1");
    assert_eq!(proof.degree(), 1);
}

#[test]
fn test_pc_proof_php_2_1() {
    // PHP(2,1): 2 pigeons, 1 hole -- UNSAT
    let clauses = vec![vec![1], vec![2], vec![-1, -2]];
    let steps = vec![
        PcStepTracked::ClauseAxiom(0), // 0: 1 + x0
        PcStepTracked::ClauseAxiom(1), // 1: 1 + x1
        PcStepTracked::ClauseAxiom(2), // 2: x0*x1
        PcStepTracked::MulVar(0, 1),   // 3: (1+x0)*x1 = x1 + x0*x1
        PcStepTracked::Add(2, 3),      // 4: x0*x1 + x1 + x0*x1 = x1
        PcStepTracked::Add(1, 4),      // 5: (1+x1) + x1 = 1
    ];
    let proof = PcProof::build(&clauses, steps).expect("should build");
    proof.verify().expect("should derive 1");
    assert_eq!(proof.degree(), 2);
    assert!(proof.verify_degree_bound(2));
    assert!(!proof.verify_degree_bound(1));
}

#[test]
fn test_pc_proof_mul_poly() {
    // Test MulPoly: derive 1 from {x, -x} using polynomial multiplication.
    let clauses = vec![vec![1], vec![-1]];
    let steps = vec![
        PcStepTracked::ClauseAxiom(0), // 0: 1+x0
        PcStepTracked::ClauseAxiom(1), // 1: x0
        // MulPoly(0, 1): (1+x0)*x0 = x0 + x0^2 = x0 + x0 = 0
        PcStepTracked::MulPoly(0, 1),
        // Now derived[2] = 0, add axiom again and weaken:
        PcStepTracked::ClauseAxiom(0), // 3: 1+x0
        PcStepTracked::ClauseAxiom(1), // 4: x0
        PcStepTracked::Add(3, 4),      // 5: 1
    ];
    let proof = PcProof::build(&clauses, steps).expect("should build");
    proof.verify().expect("should derive 1");
}

#[test]
fn test_pc_proof_boolean_axiom_step() {
    // Boolean axiom always derives 0.
    let clauses = vec![vec![1], vec![-1]];
    let steps = vec![
        PcStepTracked::BooleanAxiom(0), // 0: 0 (x^2+x)
        PcStepTracked::ClauseAxiom(0),  // 1: 1+x0
        PcStepTracked::ClauseAxiom(1),  // 2: x0
        PcStepTracked::Add(1, 2),       // 3: 1
    ];
    let proof = PcProof::build(&clauses, steps).expect("should build");
    assert!(proof.derived[0].is_zero(), "boolean axiom should give 0");
    proof.verify().expect("should derive 1");
}

#[test]
fn test_pc_proof_weaken_step() {
    let clauses = vec![vec![1], vec![-1]];
    let steps = vec![
        PcStepTracked::ClauseAxiom(0), // 0: 1+x0
        PcStepTracked::ClauseAxiom(1), // 1: x0
        PcStepTracked::Add(0, 1),      // 2: 1
    ];
    let proof = PcProof::build(&clauses, steps).expect("should build");
    proof.verify().expect("should verify");
}

#[test]
fn test_pc_proof_invalid_index_error() {
    let clauses = vec![vec![1]];
    let steps = vec![
        PcStepTracked::ClauseAxiom(0),
        PcStepTracked::Add(0, 5), // 5 does not exist
    ];
    let result = PcProof::build(&clauses, steps);
    assert!(result.is_err());
}

#[test]
fn test_pc_proof_invalid_clause_index_error() {
    let clauses = vec![vec![1]];
    let steps = vec![PcStepTracked::ClauseAxiom(99)];
    let result = PcProof::build(&clauses, steps);
    assert!(result.is_err());
}

#[test]
fn test_pc_proof_empty_error() {
    let clauses = vec![vec![1]];
    let result = PcProof::build(&clauses, vec![]);
    assert!(result.is_err());
}

#[test]
fn test_pc_proof_not_contradiction_error() {
    let clauses = vec![vec![1]];
    let steps = vec![PcStepTracked::ClauseAxiom(0)]; // 1+x0, not 1
    let proof = PcProof::build(&clauses, steps).expect("should build");
    assert!(proof.verify().is_err());
}

// =========================================================================
// Degree bound enforcement
// =========================================================================

#[test]
fn test_pc_proof_degree_bound_pass() {
    let clauses = vec![vec![1], vec![-1]];
    let steps = vec![
        PcStepTracked::ClauseAxiom(0),
        PcStepTracked::ClauseAxiom(1),
        PcStepTracked::Add(0, 1),
    ];
    let proof = PcProof::build(&clauses, steps).expect("should build");
    assert!(proof.verify_degree_bound(1));
    assert!(proof.verify_degree_bound(2));
    assert!(proof.verify_degree_bound(100));
}

#[test]
fn test_pc_proof_degree_bound_fail() {
    let clauses = vec![vec![1, 2, 3]]; // degree 3 clause
    let steps = vec![PcStepTracked::ClauseAxiom(0)];
    let proof = PcProof::build(&clauses, steps).expect("should build");
    assert!(!proof.verify_degree_bound(2));
    assert!(proof.verify_degree_bound(3));
}

// =========================================================================
// ZT03: PC Soundness
// =========================================================================

#[test]
fn test_pc_soundness_simple_unsat() {
    let clauses = vec![vec![1], vec![-1]];
    let steps = vec![
        PcStepTracked::ClauseAxiom(0),
        PcStepTracked::ClauseAxiom(1),
        PcStepTracked::Add(0, 1),
    ];
    let proof = PcProof::build(&clauses, steps).expect("should build");
    pc_soundness_gf2(&clauses, &proof).expect("should verify soundness");
}

#[test]
fn test_pc_soundness_php_2_1() {
    let clauses = vec![vec![1], vec![2], vec![-1, -2]];
    let steps = vec![
        PcStepTracked::ClauseAxiom(0),
        PcStepTracked::ClauseAxiom(1),
        PcStepTracked::ClauseAxiom(2),
        PcStepTracked::MulVar(0, 1),
        PcStepTracked::Add(2, 3),
        PcStepTracked::Add(1, 4),
    ];
    let proof = PcProof::build(&clauses, steps).expect("should build");
    pc_soundness_gf2(&clauses, &proof).expect("should verify PHP(2,1) soundness");
}

#[test]
fn test_pc_soundness_invalid_proof_fails() {
    let clauses = vec![vec![1]];
    let steps = vec![PcStepTracked::ClauseAxiom(0)]; // does not derive 1
    let proof = PcProof::build(&clauses, steps).expect("should build");
    assert!(pc_soundness_gf2(&clauses, &proof).is_err());
}

// =========================================================================
// Competition certificate compilation (partial ZT04)
// =========================================================================

#[test]
fn test_certificate_compilation_basic() {
    let clauses = vec![vec![1], vec![-1]];
    let steps = vec![
        PcStepTracked::ClauseAxiom(0),
        PcStepTracked::ClauseAxiom(1),
        PcStepTracked::Add(0, 1),
    ];
    let proof = PcProof::build(&clauses, steps).expect("should build");
    let cert = pc_to_competition_certificate(&proof, &clauses, 10_000).expect("should compile");

    // Check magic header.
    assert_eq!(&cert[0..4], &0x00_50_43_32u32.to_le_bytes());
    // Version.
    assert_eq!(&cert[4..8], &1u32.to_le_bytes());
    // Num clauses.
    assert_eq!(&cert[8..12], &2u32.to_le_bytes());
    // Num steps.
    assert_eq!(&cert[12..16], &3u32.to_le_bytes());
}

#[test]
fn test_certificate_budget_exceeded() {
    let clauses = vec![vec![1], vec![-1]];
    let steps = vec![
        PcStepTracked::ClauseAxiom(0),
        PcStepTracked::ClauseAxiom(1),
        PcStepTracked::Add(0, 1),
    ];
    let proof = PcProof::build(&clauses, steps).expect("should build");
    let result = pc_to_competition_certificate(&proof, &clauses, 1); // tiny budget
    assert!(result.is_err());
}

#[test]
fn test_certificate_invalid_proof_rejected() {
    let clauses = vec![vec![1]];
    let steps = vec![PcStepTracked::ClauseAxiom(0)];
    let proof = PcProof::build(&clauses, steps).expect("should build");
    let result = pc_to_competition_certificate(&proof, &clauses, 10_000);
    assert!(result.is_err());
}

// =========================================================================
// Integration with existing resolution_to_pc
// =========================================================================

#[test]
fn test_gf2poly_matches_legacy_encoding() {
    // Verify that Gf2Poly::from_clause matches GF2Polynomial clause encoding
    // by comparing evaluations over all assignments for small cases.
    let test_clauses: Vec<Vec<i32>> =
        vec![vec![1], vec![-1], vec![1, 2], vec![-1, -2], vec![1, -2, 3]];

    for clause in &test_clauses {
        let new_poly = Gf2Poly::from_clause(clause);
        let legacy_poly = super::polynomial_calculus::clause_to_polynomial(clause);

        // Check all assignments up to 4 variables.
        for mask in 0u32..16 {
            let assignment_new: Vec<bool> = (0..4).map(|i| (mask >> i) & 1 == 1).collect();
            let new_val = new_poly.evaluate(&assignment_new);
            let legacy_val =
                super::polynomial_calculus::evaluate_polynomial(&legacy_poly, &assignment_new);
            assert_eq!(
                new_val, legacy_val,
                "mismatch at assignment {mask:04b} for clause {clause:?}"
            );
        }
    }
}

#[test]
fn test_legacy_conversion_roundtrip() {
    let p = Gf2Poly::from_clause(&[1, 2]);
    let legacy = gf2poly_to_legacy(&p);
    let roundtrip = legacy_to_gf2poly(&legacy);
    assert_eq!(
        p, roundtrip,
        "roundtrip conversion should preserve polynomial"
    );
}

// =========================================================================
// PHP and Tseitin generators
// =========================================================================

#[test]
fn test_php_2_1_is_unsat() {
    let clauses = generate_php_cnf(2, 1).expect("valid PHP");
    let num_vars = 2u32;
    for mask in 0..(1u32 << num_vars) {
        let assignment: Vec<bool> = (0..num_vars).map(|i| (mask >> i) & 1 == 1).collect();
        let sat = clauses.iter().all(|clause| {
            clause.iter().any(|&lit| {
                let var_idx = (lit.unsigned_abs() - 1) as usize;
                let val = assignment.get(var_idx).copied().unwrap_or(false);
                if lit > 0 {
                    val
                } else {
                    !val
                }
            })
        });
        assert!(
            !sat,
            "PHP(2,1) should be UNSAT, but assignment {mask:02b} satisfies it"
        );
    }
}

#[test]
fn test_php_3_2_is_unsat() {
    let clauses = generate_php_cnf(3, 2).expect("valid PHP");
    let num_vars = 6u32;
    for mask in 0..(1u32 << num_vars) {
        let assignment: Vec<bool> = (0..num_vars).map(|i| (mask >> i) & 1 == 1).collect();
        let sat = clauses.iter().all(|clause| {
            clause.iter().any(|&lit| {
                let var_idx = (lit.unsigned_abs() - 1) as usize;
                let val = assignment.get(var_idx).copied().unwrap_or(false);
                if lit > 0 {
                    val
                } else {
                    !val
                }
            })
        });
        assert!(!sat, "PHP(3,2) should be UNSAT");
    }
}

#[test]
fn test_php_encoding_soundness() {
    let clauses = generate_php_cnf(2, 1).expect("valid PHP");
    let polys = cnf_to_gf2_system(&clauses);
    assert!(verify_encoding_soundness(&clauses, &polys, 2));
}

#[test]
fn test_tseitin_odd_parity_unsat() {
    // Triangle graph with odd total parity -> UNSAT.
    let edges = vec![(0, 1), (1, 2), (0, 2)];
    let parities = vec![true, true, true]; // sum = 3 (odd) -> UNSAT
    let (clauses, num_vars) = generate_tseitin_cnf(3, &edges, &parities);
    assert!(!clauses.is_empty());

    for mask in 0..(1u32 << num_vars) {
        let assignment: Vec<bool> = (0..num_vars).map(|i| (mask >> i) & 1 == 1).collect();
        let sat = clauses.iter().all(|clause| {
            clause.iter().any(|&lit| {
                let var_idx = (lit.unsigned_abs() - 1) as usize;
                let val = assignment.get(var_idx).copied().unwrap_or(false);
                if lit > 0 {
                    val
                } else {
                    !val
                }
            })
        });
        assert!(!sat, "Tseitin with odd parity should be UNSAT");
    }
}

#[test]
fn test_tseitin_even_parity_sat() {
    // Triangle graph with even total parity -> SAT.
    let edges = vec![(0, 1), (1, 2), (0, 2)];
    let parities = vec![true, true, false]; // sum = 2 (even) -> SAT
    let (clauses, num_vars) = generate_tseitin_cnf(3, &edges, &parities);
    assert!(!clauses.is_empty());

    let mut found_sat = false;
    for mask in 0..(1u32 << num_vars) {
        let assignment: Vec<bool> = (0..num_vars).map(|i| (mask >> i) & 1 == 1).collect();
        let sat = clauses.iter().all(|clause| {
            clause.iter().any(|&lit| {
                let var_idx = (lit.unsigned_abs() - 1) as usize;
                let val = assignment.get(var_idx).copied().unwrap_or(false);
                if lit > 0 {
                    val
                } else {
                    !val
                }
            })
        });
        if sat {
            found_sat = true;
            break;
        }
    }
    assert!(found_sat, "Tseitin with even parity should be SAT");
}

#[test]
fn test_tseitin_encoding_soundness() {
    let edges = vec![(0, 1), (1, 2), (0, 2)];
    let parities = vec![true, true, true];
    let (clauses, num_vars) = generate_tseitin_cnf(3, &edges, &parities);
    let polys = cnf_to_gf2_system(&clauses);
    assert!(verify_encoding_soundness(&clauses, &polys, num_vars));
}

// =========================================================================
// Display
// =========================================================================

#[test]
fn test_gf2poly_display() {
    assert_eq!(format!("{}", Gf2Poly::zero()), "0");
    assert_eq!(format!("{}", Gf2Poly::one()), "1");
    assert_eq!(format!("{}", Gf2Poly::variable(0)), "x0");
    assert_eq!(format!("{}", Gf2Poly::variable(3)), "x3");

    let xy = Gf2Poly::monomial(&[0, 1]);
    assert_eq!(format!("{xy}"), "x0*x1");
}

// =========================================================================
// Adversarial soundness tests (audit findings)
// =========================================================================

#[test]
fn test_soundness_weaken_constant_monomial_rejected() {
    // CRITICAL BUG (Finding 17): The Weaken rule allowed adding the constant
    // monomial 1 (empty variable set), enabling a trivial 2-step false
    // refutation of ANY formula:
    //   Step 0: BooleanAxiom(0) -> derives 0 (the zero polynomial)
    //   Step 1: Weaken(0, {}) -> derives 0 + 1 = 1 (constant 1)
    // Since the last polynomial is 1, verify() would pass, falsely claiming
    // the formula is unsatisfiable.
    //
    // This test uses a SATISFIABLE formula to demonstrate the attack.
    let satisfiable_clauses = vec![vec![1, 2]]; // (x1 v x2) is SAT

    let steps = vec![
        PcStepTracked::BooleanAxiom(0), // 0: zero polynomial
        PcStepTracked::Weaken(0, std::collections::BTreeSet::new()), // 1: add constant 1
    ];

    let result = PcProof::build(&satisfiable_clauses, steps);
    assert!(
        result.is_err(),
        "SOUNDNESS BUG: weaken with constant monomial should be rejected"
    );

    // Verify the specific error type.
    let err = result.unwrap_err();
    assert!(
        matches!(err, PcError::WeakenConstantMonomial { step: 1 }),
        "expected WeakenConstantMonomial error at step 1, got: {err:?}"
    );
}

#[test]
fn test_weaken_with_nonconstant_monomial_still_works() {
    // Weaken with a non-constant monomial (degree >= 1) should still work.
    // SOUNDNESS FIX (#3322): Weaken is now multiplicative (p * m), not additive (p + m).
    let clauses = vec![vec![1], vec![-1]];
    let steps = vec![
        PcStepTracked::ClauseAxiom(0), // 0: 1+x0
        PcStepTracked::ClauseAxiom(1), // 1: x0
        // Weaken step 0 by multiplying by monomial x1 (degree 1) -- this is sound.
        // derived[2] = (1+x0) * x1 = x1 + x0*x1
        PcStepTracked::Weaken(0, {
            let mut s = std::collections::BTreeSet::new();
            s.insert(1u32);
            s
        }),
        // Now derive 1 from clause axioms (weaken result is not needed for this).
        PcStepTracked::ClauseAxiom(0), // 3: 1+x0
        PcStepTracked::ClauseAxiom(1), // 4: x0
        PcStepTracked::Add(3, 4),      // 5: 1
    ];
    let proof = PcProof::build(&clauses, steps).expect("should build with non-constant weaken");
    proof.verify().expect("should derive 1");
}

#[test]
fn test_soundness_weaken_cannot_prove_sat_formula_unsat() {
    // After the fix, there should be no way to prove a satisfiable formula
    // unsatisfiable using only BooleanAxiom and Weaken steps.
    let sat_clauses = vec![vec![1]]; // (x1) is satisfiable with x1=true

    // Try various weaken attacks -- all should fail.
    // Attack 1: Weaken with empty set (constant 1)
    let steps1 = vec![
        PcStepTracked::BooleanAxiom(0),
        PcStepTracked::Weaken(0, std::collections::BTreeSet::new()),
    ];
    assert!(PcProof::build(&sat_clauses, steps1).is_err());

    // Attack 2: Try to reach 1 via multiplicative weakening on zero polynomial.
    // BooleanAxiom(0) = 0. Weaken(0, {0}) = 0 * x0 = 0. Still zero. Not 1.
    let steps2 = vec![
        PcStepTracked::BooleanAxiom(0),
        PcStepTracked::Weaken(0, {
            let mut s = std::collections::BTreeSet::new();
            s.insert(0u32);
            s
        }),
    ];
    let proof2 = PcProof::build(&sat_clauses, steps2).expect("should build");
    assert!(proof2.verify().is_err(), "0 * x0 = 0, not the constant 1");
}

#[test]
fn test_soundness_additive_weaken_attack_blocked() {
    // CRITICAL REGRESSION TEST (#3322): The old additive weaken rule allowed
    // a 4-step trivial false refutation of ANY satisfiable formula.
    //
    // Attack on (x1 v x2) -- a satisfiable formula:
    //   Step 0: ClauseAxiom(0) -> 1+x0+x1+x0*x1
    //   Step 1: Weaken(0, {x0}) -> old: 1+x1+x0*x1, new: (1+x0+x1+x0*x1)*x0 = x0+x0*x1
    //   Step 2: Weaken(1, {x1}) -> old: 1+x0*x1, new: (x0+x0*x1)*x1 = x0*x1
    //   Step 3: Weaken(2, {x0,x1}) -> old: 1 (!), new: x0*x1*x0*x1 = x0*x1
    //
    // With multiplicative weaken, the attack cannot reach constant 1.
    let sat_clauses = vec![vec![1, 2]]; // (x1 v x2) is SAT

    let steps = vec![
        PcStepTracked::ClauseAxiom(0), // 0: 1+x0+x1+x0*x1
        PcStepTracked::Weaken(0, {
            let mut s = std::collections::BTreeSet::new();
            s.insert(0u32);
            s
        }), // 1: (1+x0+x1+x0*x1)*x0 = x0+x0*x1
        PcStepTracked::Weaken(1, {
            let mut s = std::collections::BTreeSet::new();
            s.insert(1u32);
            s
        }), // 2: (x0+x0*x1)*x1 = x0*x1
        PcStepTracked::Weaken(2, {
            let mut s = std::collections::BTreeSet::new();
            s.insert(0u32);
            s.insert(1u32);
            s
        }), // 3: x0*x1 * x0*x1 = x0*x1 (idempotent in GF(2))
    ];

    let proof = PcProof::build(&sat_clauses, steps).expect("should build");
    assert!(
        proof.verify().is_err(),
        "SOUNDNESS BUG: additive weaken attack should not derive 1 from SAT formula"
    );
    // Final polynomial should be x0*x1, not 1.
    assert!(
        !proof.derived.last().unwrap().is_one(),
        "last polynomial should not be constant 1"
    );
}

#[test]
fn test_soundness_weaken_resolution_cannot_derive_false() {
    use std::collections::BTreeSet;

    let sat_clauses = vec![vec![1, 2]]; // (x1 v x2) is satisfiable

    let steps = vec![
        PcStepTracked::ClauseAxiom(0), // 0: 1+x0+x1+x0*x1
        PcStepTracked::MulVar(0, 0),   // 1: x0+x0*x1
        PcStepTracked::Add(0, 1),      // 2: 1+x1
        PcStepTracked::MulVar(2, 1),   // 3: 0
        PcStepTracked::Weaken(2, {
            let mut mono = BTreeSet::new();
            mono.insert(0u32);
            mono
        }), // 4: x0+x0*x1
        PcStepTracked::Add(1, 4),      // 5: 0
    ];

    let proof = PcProof::build(&sat_clauses, steps).expect("should build");
    assert!(
        proof.derived.last().unwrap().is_zero(),
        "attack collapses to 0"
    );
    assert!(
        proof.verify().is_err(),
        "SOUNDNESS BUG: attack should not derive 1 from SAT formula"
    );
}

// =========================================================================
// #3316: Pipeline integration — ProofFormat::PolynomialCalculus
// =========================================================================

#[test]
fn test_pipeline_detect_pc_text_format() {
    use crate::sat_verify::pipeline::{detect_format, ProofFormat};
    let data = b"PC-GF2 v1\nCLAUSES 2\nSTEPS 3\nMAXDEG 1\n";
    assert_eq!(detect_format(data), ProofFormat::PolynomialCalculus);
}

#[test]
fn test_pipeline_detect_pc_binary_magic() {
    use crate::sat_verify::pipeline::{detect_format, ProofFormat};
    let mut data = vec![0u8; 20];
    data[0..4].copy_from_slice(&0x00_50_43_32u32.to_le_bytes());
    assert_eq!(detect_format(&data), ProofFormat::PolynomialCalculus);
}

#[test]
fn test_pipeline_pc_format_display() {
    use crate::sat_verify::pipeline::ProofFormat;
    assert_eq!(ProofFormat::PolynomialCalculus.to_string(), "PC/GF(2)");
}

#[test]
fn test_pipeline_proof_input_pc_text_format() {
    use crate::sat_verify::pipeline::{ProofFormat, ProofInput};
    let input = ProofInput::PcText("PC-GF2 v1".to_string());
    assert_eq!(input.format(), ProofFormat::PolynomialCalculus);
    assert_eq!(input.size_bytes(), 9);
}

#[test]
fn test_pipeline_proof_input_pc_binary_format() {
    use crate::sat_verify::pipeline::{ProofFormat, ProofInput};
    let input = ProofInput::PcBinary(vec![0x32, 0x43, 0x50, 0x00]);
    assert_eq!(input.format(), ProofFormat::PolynomialCalculus);
    assert_eq!(input.size_bytes(), 4);
}

// =========================================================================
// #3316: CheckableGf2PcProof via ProofChecker trait
// =========================================================================

#[test]
fn test_checkable_gf2_pc_proof_valid() {
    use crate::sat_verify::proof_checker::{CheckableGf2PcProof, ProofChecker};

    let clauses = vec![vec![1], vec![-1]];
    let steps = vec![
        PcStepTracked::ClauseAxiom(0),
        PcStepTracked::ClauseAxiom(1),
        PcStepTracked::Add(0, 1),
    ];
    let checkable = CheckableGf2PcProof { clauses, steps };
    assert!(checkable.check().is_ok());
    assert_eq!(checkable.proof_size(), 3);
}

#[test]
fn test_checkable_gf2_pc_proof_not_refutation() {
    use crate::sat_verify::proof_checker::{CheckableGf2PcProof, ProofChecker};

    let clauses = vec![vec![1, 2]]; // SAT
    let steps = vec![PcStepTracked::ClauseAxiom(0)];
    let checkable = CheckableGf2PcProof { clauses, steps };
    assert!(checkable.check().is_err());
}

#[test]
fn test_checkable_gf2_pc_proof_php_2_1() {
    use crate::sat_verify::proof_checker::{CheckableGf2PcProof, ProofChecker};

    let clauses = vec![vec![1], vec![2], vec![-1, -2]];
    let steps = vec![
        PcStepTracked::ClauseAxiom(0),
        PcStepTracked::ClauseAxiom(1),
        PcStepTracked::ClauseAxiom(2),
        PcStepTracked::MulVar(0, 1),
        PcStepTracked::Add(2, 3),
        PcStepTracked::Add(1, 4),
    ];
    let checkable = CheckableGf2PcProof { clauses, steps };
    assert!(checkable.check().is_ok());
    assert_eq!(checkable.proof_size(), 6);
}

// =========================================================================
// #3316: All proof rules in one derivation
// =========================================================================

#[test]
fn test_all_rule_types_combined() {
    let clauses = vec![vec![1], vec![-1]];
    let steps = vec![
        PcStepTracked::BooleanAxiom(0), // 0: 0
        PcStepTracked::ClauseAxiom(0),  // 1: 1+x0
        PcStepTracked::ClauseAxiom(1),  // 2: x0
        PcStepTracked::MulVar(1, 1),    // 3: (1+x0)*x1 = x1+x0*x1
        PcStepTracked::MulPoly(1, 2),   // 4: (1+x0)*x0 = 0
        PcStepTracked::Add(1, 2),       // 5: 1
    ];
    let proof = PcProof::build(&clauses, steps).expect("should build");
    proof.verify().expect("should verify");
    assert!(proof.derived[0].is_zero(), "boolean axiom gives 0");
    assert!(proof.derived[4].is_zero(), "mul_poly gives 0");
    assert!(proof.derived[5].is_one(), "add gives contradiction");
}

// =========================================================================
// #3316: Empty clause = immediate contradiction
// =========================================================================

#[test]
fn test_empty_clause_immediate_contradiction() {
    let p = Gf2Poly::from_clause(&[]);
    assert!(p.is_one(), "empty clause polynomial should be 1");

    let clauses: Vec<Vec<i32>> = vec![vec![]];
    let steps = vec![PcStepTracked::ClauseAxiom(0)];
    let proof = PcProof::build(&clauses, steps).expect("should build");
    proof
        .verify()
        .expect("empty clause is immediate contradiction");
}

// =========================================================================
// #3316: Certificate compilation for PHP(2,1)
// =========================================================================

#[test]
fn test_certificate_php_2_1_header() {
    let clauses = vec![vec![1], vec![2], vec![-1, -2]];
    let steps = vec![
        PcStepTracked::ClauseAxiom(0),
        PcStepTracked::ClauseAxiom(1),
        PcStepTracked::ClauseAxiom(2),
        PcStepTracked::MulVar(0, 1),
        PcStepTracked::Add(2, 3),
        PcStepTracked::Add(1, 4),
    ];
    let proof = PcProof::build(&clauses, steps).expect("should build");
    let cert = pc_to_competition_certificate(&proof, &clauses, 100_000).expect("compile");

    // Verify header fields
    let magic = u32::from_le_bytes([cert[0], cert[1], cert[2], cert[3]]);
    assert_eq!(magic, 0x0050_4332);
    let version = u32::from_le_bytes([cert[4], cert[5], cert[6], cert[7]]);
    assert_eq!(version, 1);
    let nclauses = u32::from_le_bytes([cert[8], cert[9], cert[10], cert[11]]);
    assert_eq!(nclauses, 3);
    let nsteps = u32::from_le_bytes([cert[12], cert[13], cert[14], cert[15]]);
    assert_eq!(nsteps, 6);
    let maxdeg = u32::from_le_bytes([cert[16], cert[17], cert[18], cert[19]]);
    assert_eq!(maxdeg, 2);
}

// =========================================================================
// #3316: Encoding correctness — exhaustive verification
// =========================================================================

#[test]
fn test_encoding_soundness_3var_formulas() {
    // Test multiple 3-variable formulas
    let formulas: Vec<Vec<Vec<i32>>> = vec![
        vec![vec![1, 2], vec![-1, 3], vec![-2, -3]],
        vec![vec![1, 2, 3], vec![-1, -2], vec![-2, -3], vec![-1, -3]],
        vec![vec![1], vec![-1, 2], vec![-2, 3], vec![-3]],
    ];
    for clauses in &formulas {
        let polys = cnf_to_gf2_system(clauses);
        assert!(
            verify_encoding_soundness(clauses, &polys, 3),
            "encoding unsound for {clauses:?}"
        );
    }
}

// =========================================================================
// #3316: Degree tracking accuracy
// =========================================================================

#[test]
fn test_degree_tracking_mul_var_increases() {
    // mul_var can increase degree
    let clauses = vec![vec![1]];
    let steps = vec![
        PcStepTracked::ClauseAxiom(0), // degree 1: 1+x0
        PcStepTracked::MulVar(0, 1),   // degree 2: (1+x0)*x1
        PcStepTracked::MulVar(1, 2),   // degree 3: ((1+x0)*x1)*x2
    ];
    let proof = PcProof::build(&clauses, steps).expect("should build");
    assert_eq!(proof.degree(), 3);
    assert!(proof.verify_degree_bound(3));
    assert!(!proof.verify_degree_bound(2));
}
