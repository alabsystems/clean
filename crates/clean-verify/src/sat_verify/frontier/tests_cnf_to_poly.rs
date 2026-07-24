// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for CNF-to-polynomial translation module.

use super::cnf_to_poly::*;
use super::gf2_algebra::Gf2Poly;

// =========================================================================
// CnfFormula construction
// =========================================================================

#[test]
fn test_cnf_formula_basic() {
    let formula = CnfFormula::new(vec![vec![1, 2], vec![-1, -2]]).expect("valid CNF");
    assert_eq!(formula.num_vars(), 2);
    assert_eq!(formula.num_clauses(), 2);
    assert_eq!(formula.max_width(), 2);
    assert_eq!(formula.expected_max_degree(), 2);
}

#[test]
fn test_cnf_formula_single_clause() {
    let formula = CnfFormula::new(vec![vec![1]]).expect("valid CNF");
    assert_eq!(formula.num_vars(), 1);
    assert_eq!(formula.num_clauses(), 1);
    assert_eq!(formula.max_width(), 1);
}

#[test]
fn test_cnf_formula_large_variables() {
    let formula = CnfFormula::new(vec![vec![100, -200]]).expect("valid CNF");
    assert_eq!(formula.num_vars(), 200);
    assert_eq!(formula.max_width(), 2);
}

#[test]
fn test_cnf_formula_rejects_zero_literal() {
    let result = CnfFormula::new(vec![vec![1, 0, 2]]);
    assert!(result.is_err());
}

#[test]
fn test_cnf_formula_rejects_empty_clause() {
    let result = CnfFormula::new(vec![vec![1, 2], vec![]]);
    assert!(result.is_err());
}

#[test]
fn test_cnf_formula_from_raw() {
    let formula = CnfFormula::from_raw(vec![vec![1], vec![-1]], 1);
    assert_eq!(formula.num_vars(), 1);
    assert_eq!(formula.num_clauses(), 2);
}

// =========================================================================
// translate_clause
// =========================================================================

#[test]
fn test_translate_clause_positive_literal() {
    let t = translate_clause(&[1], 0).expect("valid clause");
    assert_eq!(t.clause, vec![1]);
    assert_eq!(t.clause_idx, 0);
    assert_eq!(t.degree, 1);
    assert_eq!(t.variables, vec![0]);
    assert_eq!(t.polarities, vec![true]);
    // (x1) -> (1 - x0) = 1 + x0
    let expected = Gf2Poly::one().add(&Gf2Poly::variable(0));
    assert_eq!(t.polynomial, expected);
}

#[test]
fn test_translate_clause_negative_literal() {
    let t = translate_clause(&[-1], 0).expect("valid clause");
    assert_eq!(t.polarities, vec![false]);
    assert_eq!(t.polynomial, Gf2Poly::variable(0));
}

#[test]
fn test_translate_clause_two_literals_mixed() {
    let t = translate_clause(&[1, -2], 0).expect("valid clause");
    assert_eq!(t.variables, vec![0, 1]);
    assert_eq!(t.polarities, vec![true, false]);
    assert_eq!(t.degree, 2);
}

#[test]
fn test_translate_clause_three_literals() {
    let t = translate_clause(&[1, 2, 3], 0).expect("valid clause");
    assert_eq!(t.degree, 3);
    assert_eq!(t.variables, vec![0, 1, 2]);
    assert!(t.polarities.iter().all(|&p| p));
}

#[test]
fn test_translate_clause_rejects_zero() {
    let result = translate_clause(&[1, 0, 2], 5);
    assert!(result.is_err());
}

// =========================================================================
// translate_cnf
// =========================================================================

#[test]
fn test_translate_cnf_basic() {
    let formula = CnfFormula::new(vec![vec![1], vec![-1]]).expect("valid CNF");
    let translations = translate_cnf(&formula).expect("valid translation");
    assert_eq!(translations.len(), 2);
    assert_eq!(translations[0].clause_idx, 0);
    assert_eq!(translations[1].clause_idx, 1);
}

#[test]
fn test_translate_cnf_preserves_polynomial() {
    let formula = CnfFormula::new(vec![vec![1, 2], vec![-1, -2]]).expect("valid CNF");
    let translations = translate_cnf(&formula).expect("valid translation");
    assert_eq!(translations[0].polynomial, Gf2Poly::from_clause(&[1, 2]));
    assert_eq!(translations[1].polynomial, Gf2Poly::from_clause(&[-1, -2]));
}

#[test]
fn test_translate_cnf_polynomials_helper() {
    let formula = CnfFormula::new(vec![vec![1], vec![-1]]).expect("valid CNF");
    let polys = translate_cnf_polynomials(&formula).expect("valid translation");
    assert_eq!(polys.len(), 2);
    assert_eq!(polys[0], Gf2Poly::from_clause(&[1]));
    assert_eq!(polys[1], Gf2Poly::from_clause(&[-1]));
}

// =========================================================================
// XOR constraint generation
// =========================================================================

#[test]
fn test_xor_cnf_single_constraint() {
    // x1 XOR x2 = 1
    let (clauses, num_vars) = generate_xor_cnf(2, &[(vec![1, 2], true)]);
    assert_eq!(num_vars, 2);
    // XOR with 2 variables, parity true: excludes assignments with even parity.
    // (0,0) has parity false -> clause needed: (x1, x2) [exclude both false]
    // (1,1) has parity false -> clause needed: (-x1, -x2) [exclude both true]
    assert_eq!(clauses.len(), 2);
}

#[test]
fn test_xor_cnf_parity_false() {
    // x1 XOR x2 = 0 (meaning x1 = x2)
    let (clauses, _) = generate_xor_cnf(2, &[(vec![1, 2], false)]);
    // Excludes assignments with odd parity: (0,1) and (1,0).
    assert_eq!(clauses.len(), 2);
}

#[test]
fn test_unsat_xor_system_n2() {
    // n=2: x1 XOR x2 = 0, x1 XOR x2 = 1 -> contradictory
    let (clauses, num_vars) = generate_unsat_xor_system(2);
    assert!(!clauses.is_empty());

    // Verify UNSAT by exhaustive check.
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
        assert!(!sat, "UNSAT XOR system(2) should be unsatisfiable");
    }
}

#[test]
fn test_unsat_xor_system_n3() {
    let (clauses, num_vars) = generate_unsat_xor_system(3);
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
        assert!(!sat, "UNSAT XOR system(3) should be unsatisfiable");
    }
}

#[test]
fn test_unsat_xor_system_n4() {
    let (clauses, num_vars) = generate_unsat_xor_system(4);
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
        assert!(!sat, "UNSAT XOR system(4) should be unsatisfiable");
    }
}

#[test]
fn test_xor_cnf_encoding_soundness() {
    // Verify encoding soundness for a small XOR system.
    let (clauses, num_vars) = generate_xor_cnf(3, &[(vec![1, 2, 3], true)]);
    let formula = CnfFormula::from_raw(clauses.clone(), num_vars);
    let translations = translate_cnf(&formula).expect("valid translation");
    let result = verify_translation(&formula, &translations);
    assert!(result.expect("should verify").then_some(true).is_some());
}

// =========================================================================
// Translation verification
// =========================================================================

#[test]
fn test_verify_translation_unit_clauses() {
    let formula = CnfFormula::new(vec![vec![1], vec![-1]]).expect("valid CNF");
    let translations = translate_cnf(&formula).expect("valid translation");
    assert!(verify_translation(&formula, &translations).expect("should verify"));
}

#[test]
fn test_verify_translation_php_2_1() {
    let formula = CnfFormula::new(vec![vec![1], vec![2], vec![-1, -2]]).expect("valid CNF");
    let translations = translate_cnf(&formula).expect("valid translation");
    assert!(verify_translation(&formula, &translations).expect("should verify"));
}

#[test]
fn test_verify_translation_sat_formula() {
    let formula = CnfFormula::new(vec![vec![1, 2]]).expect("valid CNF");
    let translations = translate_cnf(&formula).expect("valid translation");
    assert!(verify_translation(&formula, &translations).expect("should verify"));
}

#[test]
fn test_verify_translation_wrong_polynomial() {
    let formula = CnfFormula::new(vec![vec![1]]).expect("valid CNF");
    // Create a wrong translation.
    let wrong = vec![ClauseTranslation {
        polynomial: Gf2Poly::variable(1), // wrong!
        clause: vec![1],
        clause_idx: 0,
        degree: 1,
        variables: vec![1],
        polarities: vec![true],
    }];
    assert!(!verify_translation(&formula, &wrong).expect("should verify"));
}

#[test]
fn test_verify_translation_too_many_vars() {
    let formula = CnfFormula::from_raw(vec![vec![21]], 21);
    let translations = translate_cnf(&formula).expect("valid translation");
    let result = verify_translation(&formula, &translations);
    assert!(result.is_err());
}

#[test]
fn test_verify_translation_length_mismatch() {
    let formula = CnfFormula::new(vec![vec![1], vec![-1]]).expect("valid CNF");
    let translations = vec![]; // wrong length
    assert!(!verify_translation(&formula, &translations).expect("should verify"));
}
