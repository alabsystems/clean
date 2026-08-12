// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the pseudo-Boolean constraint verification kernel.

use super::certificate::{export_certificate, export_veripb, hash_formula};
use super::cnf_bridge::{cnf_to_pb, is_cnf_representable, pb_to_cnf};
use super::normalize::{normalize, saturate, simplify_formula};
use super::opb_format::{parse_opb, write_opb};
use super::rules::{verify_pb_proof, verify_rule, PbRule};
use super::types::{PbConstraint, PbFormula, PbObjective};
use super::veripb::{cutting_planes_to_veripb, VeriPbProof, VeriPbStep};
use super::PbError;
use crate::sat_verify::proof_complexity::cutting_planes::{CpInequality, CuttingPlanesProof};

// ============================================================
// PbConstraint creation and properties
// ============================================================

#[test]
fn test_pb_constraint_new() {
    let c = PbConstraint::new(vec![(1, 1), (2, 2), (3, 3)], 4);
    assert_eq!(c.terms.len(), 3);
    assert_eq!(c.degree, 4);
}

#[test]
fn test_pb_constraint_is_clause() {
    // x1 + x2 + x3 >= 1 is a clause
    let clause = PbConstraint::new(vec![(1, 1), (1, 2), (1, 3)], 1);
    assert!(clause.is_clause());

    // 2*x1 + x2 >= 1 is NOT a clause (coefficient != 1)
    let not_clause = PbConstraint::new(vec![(2, 1), (1, 2)], 1);
    assert!(!not_clause.is_clause());

    // x1 + x2 >= 2 is NOT a clause (degree != 1)
    let cardinality = PbConstraint::new(vec![(1, 1), (1, 2)], 2);
    assert!(!cardinality.is_clause());
}

#[test]
fn test_pb_constraint_is_cardinality() {
    let card = PbConstraint::new(vec![(1, 1), (1, 2), (1, 3)], 2);
    assert!(card.is_cardinality());

    let clause = PbConstraint::new(vec![(1, 1), (1, 2)], 1);
    assert!(!clause.is_cardinality()); // degree is 1, not > 1

    let weighted = PbConstraint::new(vec![(2, 1), (1, 2)], 2);
    assert!(!weighted.is_cardinality()); // coefficient != 1
}

#[test]
fn test_pb_constraint_to_clause() {
    let clause = PbConstraint::new(vec![(1, 1), (1, -2), (1, 3)], 1);
    let lits = clause.to_clause().expect("should be convertible to clause");
    assert_eq!(lits, vec![1, -2, 3]);

    let non_clause = PbConstraint::new(vec![(2, 1), (1, 2)], 1);
    assert!(non_clause.to_clause().is_none());
}

#[test]
fn test_pb_constraint_from_clause() {
    let c = PbConstraint::from_clause(&[1, -2, 3]);
    assert!(c.is_clause());
    assert_eq!(c.terms, vec![(1, 1), (1, -2), (1, 3)]);
    assert_eq!(c.degree, 1);
}

#[test]
fn test_pb_constraint_clause_roundtrip() {
    let original = vec![1, -3, 5, -7];
    let c = PbConstraint::from_clause(&original);
    let recovered = c.to_clause().expect("roundtrip should work");
    assert_eq!(recovered, original);
}

// ============================================================
// Normalization
// ============================================================

#[test]
fn test_pb_constraint_normalize_removes_zeros() {
    let mut c = PbConstraint::new(vec![(1, 1), (0, 2), (3, 3)], 2);
    c.normalize();
    assert_eq!(c.terms.len(), 2);
    assert!(c.terms.iter().all(|&(coeff, _)| coeff > 0));
}

#[test]
fn test_pb_constraint_normalize_combines_duplicates() {
    let mut c = PbConstraint::new(vec![(1, 1), (2, 1), (3, 2)], 4);
    c.normalize();
    // Literal 1 should have coefficient 3
    let coeff_1: i64 = c
        .terms
        .iter()
        .filter(|&&(_, lit)| lit == 1)
        .map(|&(c, _)| c)
        .sum();
    assert_eq!(coeff_1, 3);
}

#[test]
fn test_pb_constraint_normalize_flips_negative() {
    // -2 * x1 >= 1 becomes 2 * ~x1 >= 3
    let mut c = PbConstraint::new(vec![(-2, 1)], 1);
    c.normalize();
    assert_eq!(c.terms.len(), 1);
    assert_eq!(c.terms[0], (2, -1)); // flipped to ~x1
    assert_eq!(c.degree, 3); // 1 + 2 = 3
}

// ============================================================
// Evaluation
// ============================================================

#[test]
fn test_pb_constraint_evaluate_satisfied() {
    // 2*x1 + 3*x2 >= 3
    let c = PbConstraint::new(vec![(2, 1), (3, 2)], 3);
    // x1=true, x2=true -> 2+3=5 >= 3
    let assignment = vec![None, Some(true), Some(true)]; // 1-indexed
    assert_eq!(c.evaluate(&assignment), Some(true));
}

#[test]
fn test_pb_constraint_evaluate_falsified() {
    // 2*x1 + 3*x2 >= 6
    let c = PbConstraint::new(vec![(2, 1), (3, 2)], 6);
    // x1=true, x2=true -> 2+3=5 < 6
    let assignment = vec![None, Some(true), Some(true)];
    assert_eq!(c.evaluate(&assignment), Some(false));
}

#[test]
fn test_pb_constraint_evaluate_undetermined() {
    // 2*x1 + 3*x2 >= 3
    let c = PbConstraint::new(vec![(2, 1), (3, 2)], 3);
    // x1=true, x2=unassigned -> sum=2, max_remaining=3, 2+3=5 >= 3 but 2 < 3
    let assignment = vec![None, Some(true), None];
    assert_eq!(c.evaluate(&assignment), None);
}

#[test]
fn test_pb_constraint_evaluate_negated_literal() {
    // 2*~x1 + 3*x2 >= 3 (literal -1 means ~x1)
    let c = PbConstraint::new(vec![(2, -1), (3, 2)], 3);
    // x1=false (~x1=true), x2=true -> 2+3=5 >= 3
    let assignment = vec![None, Some(false), Some(true)];
    assert_eq!(c.evaluate(&assignment), Some(true));
}

// ============================================================
// Slack
// ============================================================

#[test]
fn test_pb_constraint_slack_positive() {
    // 2*x1 + 3*x2 >= 3; x1=true,x2=true -> slack = 5 - 3 = 2
    let c = PbConstraint::new(vec![(2, 1), (3, 2)], 3);
    let assignment = vec![None, Some(true), Some(true)];
    assert_eq!(c.slack(&assignment), 2);
}

#[test]
fn test_pb_constraint_slack_negative() {
    // 2*x1 + 3*x2 >= 6; x1=true,x2=false -> slack = 2 - 6 = -4
    let c = PbConstraint::new(vec![(2, 1), (3, 2)], 6);
    let assignment = vec![None, Some(true), Some(false)];
    assert_eq!(c.slack(&assignment), -4);
}

// ============================================================
// Propagation
// ============================================================

#[test]
fn test_pb_constraint_propagate_forces_literal() {
    // 3*x1 + 2*x2 + 1*x3 >= 5
    // If x3=false, then we need 3*x1 + 2*x2 >= 5.
    // Without x1: max = 2 < 5, so x1 is forced.
    // Without x2: max = 3 < 5, so x2 is forced.
    let c = PbConstraint::new(vec![(3, 1), (2, 2), (1, 3)], 5);
    let assignment = vec![None, None, None, Some(false)]; // x3 = false
    let forced = c.propagate(&assignment);
    assert!(forced.contains(&1));
    assert!(forced.contains(&2));
}

#[test]
fn test_pb_constraint_propagate_no_forced() {
    // x1 + x2 + x3 >= 1 with nothing assigned: no literal is forced.
    let c = PbConstraint::new(vec![(1, 1), (1, 2), (1, 3)], 1);
    let assignment = vec![None, None, None, None];
    let forced = c.propagate(&assignment);
    assert!(forced.is_empty());
}

#[test]
fn test_pb_constraint_propagate_already_satisfied() {
    // 2*x1 + 3*x2 >= 3; x2=true -> sum=3 >= 3, no forcing needed.
    let c = PbConstraint::new(vec![(2, 1), (3, 2)], 3);
    let assignment = vec![None, None, Some(true)];
    let forced = c.propagate(&assignment);
    assert!(forced.is_empty());
}

// ============================================================
// Formula and Objective
// ============================================================

#[test]
fn test_pb_formula_add_constraints() {
    let mut f = PbFormula::new(3);
    let i0 = f.add_constraint(PbConstraint::new(vec![(1, 1), (1, 2)], 1));
    let i1 = f.add_constraint(PbConstraint::new(vec![(1, 2), (1, 3)], 1));
    assert_eq!(i0, 0);
    assert_eq!(i1, 1);
    assert_eq!(f.constraints.len(), 2);
}

#[test]
fn test_pb_objective_minimize() {
    let obj = PbObjective::minimize(vec![(3, 1), (2, 2)]);
    assert!(obj.minimize);
    let assignment = vec![None, Some(true), Some(false)];
    assert_eq!(obj.evaluate(&assignment), 3);
}

#[test]
fn test_pb_objective_maximize() {
    let obj = PbObjective::maximize(vec![(3, 1), (2, 2)]);
    assert!(!obj.minimize);
    let assignment = vec![None, Some(true), Some(true)];
    assert_eq!(obj.evaluate(&assignment), 5);
}

// ============================================================
// Proof rules: Addition
// ============================================================

#[test]
fn test_rule_addition() {
    let mut formula = PbFormula::new(3);
    formula.add_constraint(PbConstraint::new(vec![(1, 1), (1, 2)], 1));
    formula.add_constraint(PbConstraint::new(vec![(1, 2), (1, 3)], 1));

    let derived = vec![
        PbConstraint::new(vec![(1, 1), (1, 2)], 1),
        PbConstraint::new(vec![(1, 2), (1, 3)], 1),
    ];

    let result = verify_rule(&derived, &formula, &PbRule::Addition { left: 0, right: 1 })
        .expect("addition should succeed");

    // x1 + 2*x2 + x3 >= 2
    assert_eq!(result.degree, 2);
    let coeff_map: std::collections::HashMap<i32, i64> =
        result.terms.iter().map(|&(c, l)| (l, c)).collect();
    assert_eq!(coeff_map.get(&1), Some(&1));
    assert_eq!(coeff_map.get(&2), Some(&2));
    assert_eq!(coeff_map.get(&3), Some(&1));
}

// ============================================================
// Proof rules: Multiplication
// ============================================================

#[test]
fn test_rule_multiplication() {
    let formula = PbFormula::new(2);
    let derived = vec![PbConstraint::new(vec![(1, 1), (2, 2)], 3)];

    let result = verify_rule(
        &derived,
        &formula,
        &PbRule::Multiplication {
            constraint: 0,
            scalar: 3,
        },
    )
    .expect("multiplication should succeed");

    assert_eq!(result.degree, 9);
    assert_eq!(result.terms[0], (3, 1));
    assert_eq!(result.terms[1], (6, 2));
}

#[test]
fn test_rule_multiplication_nonpositive_fails() {
    let formula = PbFormula::new(1);
    let derived = vec![PbConstraint::new(vec![(1, 1)], 1)];

    let err = verify_rule(
        &derived,
        &formula,
        &PbRule::Multiplication {
            constraint: 0,
            scalar: 0,
        },
    )
    .unwrap_err();
    assert!(matches!(err, PbError::NonPositiveScalar(0)));

    let err = verify_rule(
        &derived,
        &formula,
        &PbRule::Multiplication {
            constraint: 0,
            scalar: -1,
        },
    )
    .unwrap_err();
    assert!(matches!(err, PbError::NonPositiveScalar(-1)));
}

// ============================================================
// Proof rules: Division
// ============================================================

#[test]
fn test_rule_division_ceiling() {
    let formula = PbFormula::new(2);
    let derived = vec![PbConstraint::new(vec![(2, 1), (3, 2)], 5)];

    let result = verify_rule(
        &derived,
        &formula,
        &PbRule::Division {
            constraint: 0,
            divisor: 2,
        },
    )
    .expect("division should succeed");

    // ceil(2/2)=1, ceil(3/2)=2, ceil(5/2)=3
    assert_eq!(result.terms[0], (1, 1));
    assert_eq!(result.terms[1], (2, 2));
    assert_eq!(result.degree, 3);
}

#[test]
fn test_rule_division_nonpositive_fails() {
    let formula = PbFormula::new(1);
    let derived = vec![PbConstraint::new(vec![(1, 1)], 1)];

    let err = verify_rule(
        &derived,
        &formula,
        &PbRule::Division {
            constraint: 0,
            divisor: 0,
        },
    )
    .unwrap_err();
    assert!(matches!(err, PbError::NonPositiveDivisor(0)));
}

// ============================================================
// Proof rules: Saturation
// ============================================================

#[test]
fn test_rule_saturation() {
    let formula = PbFormula::new(3);
    // 5*x1 + 3*x2 + 1*x3 >= 3
    let derived = vec![PbConstraint::new(vec![(5, 1), (3, 2), (1, 3)], 3)];

    let result =
        verify_rule(&derived, &formula, &PbRule::Saturation(0)).expect("saturation should succeed");

    // min(5,3)=3, min(3,3)=3, min(1,3)=1
    assert_eq!(result.terms[0], (3, 1));
    assert_eq!(result.terms[1], (3, 2));
    assert_eq!(result.terms[2], (1, 3));
    assert_eq!(result.degree, 3);
}

#[test]
fn test_rule_saturation_soundness_on_php() {
    // PHP(2,1): 2 pigeons, 1 hole. Each pigeon must go somewhere.
    // p1_h1 + p2_h1 <= 1 (at most one pigeon per hole)
    // In PB form: ~p1_h1 + ~p2_h1 >= 1 (i.e., 1*~x1 + 1*~x2 >= 1)
    // Also: p1_h1 >= 1 and p2_h1 >= 1 (each pigeon must go to hole 1)
    //
    // After adding p1>=1 and p2>=1: x1 + x2 >= 2
    // Adding with the hole constraint (~x1 + ~x2 >= 1): nothing useful directly.
    // But this tests that saturation doesn't break valid constraints.
    let c = PbConstraint::new(vec![(10, 1), (10, 2)], 3);
    let formula = PbFormula::new(2);
    let derived = vec![c];

    let sat = verify_rule(&derived, &formula, &PbRule::Saturation(0))
        .expect("saturation on PHP encoding");

    // Both coefficients capped at 3.
    assert_eq!(sat.terms[0], (3, 1));
    assert_eq!(sat.terms[1], (3, 2));
    assert_eq!(sat.degree, 3);

    // Verify soundness: any assignment satisfying original satisfies saturated.
    for x1 in [false, true] {
        for x2 in [false, true] {
            let orig_sum = if x1 { 10 } else { 0 } + if x2 { 10 } else { 0 };
            let sat_sum = if x1 { 3 } else { 0 } + if x2 { 3 } else { 0 };
            if orig_sum >= 3 {
                assert!(sat_sum >= 3, "saturation unsound for x1={x1}, x2={x2}");
            }
        }
    }
}

// ============================================================
// Proof rules: Rounding
// ============================================================

#[test]
fn test_rule_rounding() {
    let formula = PbFormula::new(3);
    // 6*x1 + 4*x2 + 2*x3 >= 8 -> GCD=2 -> 3*x1 + 2*x2 + 1*x3 >= 4
    let derived = vec![PbConstraint::new(vec![(6, 1), (4, 2), (2, 3)], 8)];

    let result =
        verify_rule(&derived, &formula, &PbRule::Rounding(0)).expect("rounding should succeed");

    assert_eq!(result.terms[0], (3, 1));
    assert_eq!(result.terms[1], (2, 2));
    assert_eq!(result.terms[2], (1, 3));
    assert_eq!(result.degree, 4);
}

#[test]
fn test_rule_rounding_noop_when_gcd_one() {
    let formula = PbFormula::new(2);
    // 3*x1 + 5*x2 >= 4 -> GCD=1 -> no change
    let original = PbConstraint::new(vec![(3, 1), (5, 2)], 4);
    let derived = vec![original.clone()];

    let result =
        verify_rule(&derived, &formula, &PbRule::Rounding(0)).expect("rounding should succeed");

    assert_eq!(result, original);
}

#[test]
fn test_rule_rounding_soundness() {
    // Verify rounding soundness on a concrete example.
    // 4*x1 + 6*x2 >= 7 -> GCD=2 -> 2*x1 + 3*x2 >= ceil(7/2) = 4
    let original = PbConstraint::new(vec![(4, 1), (6, 2)], 7);
    let formula = PbFormula::new(2);
    let derived = vec![original.clone()];

    let rounded =
        verify_rule(&derived, &formula, &PbRule::Rounding(0)).expect("rounding should succeed");

    assert_eq!(rounded.degree, 4); // ceil(7/2) = 4

    // Check soundness: every satisfying assignment of original satisfies rounded.
    for x1 in [false, true] {
        for x2 in [false, true] {
            let orig_sum = if x1 { 4 } else { 0 } + if x2 { 6 } else { 0 };
            let round_sum = if x1 { 2 } else { 0 } + if x2 { 3 } else { 0 };
            if orig_sum >= 7 {
                assert!(
                    round_sum >= 4,
                    "rounding unsound for x1={x1}, x2={x2}: {round_sum} < 4"
                );
            }
        }
    }
}

// ============================================================
// Proof rules: Generalized Resolution
// ============================================================

#[test]
fn test_rule_generalized_resolution() {
    // L: 2*x1 + 3*x2 >= 4 (x1 appears positively with coeff 2)
    // R: 1*~x1 + 2*x3 >= 2 (x1 appears negatively with coeff 1)
    let formula = PbFormula::new(3);
    let derived = vec![
        PbConstraint::new(vec![(2, 1), (3, 2)], 4),
        PbConstraint::new(vec![(1, -1), (2, 3)], 2),
    ];

    let result = verify_rule(
        &derived,
        &formula,
        &PbRule::GeneralizedResolution {
            left: 0,
            right: 1,
            var: 1,
        },
    )
    .expect("generalized resolution should succeed");

    // Multiply L by c_R=1: 2*x1 + 3*x2 >= 4
    // Multiply R by c_L=2: 2*~x1 + 4*x3 >= 4
    // Add: 2*x1 + 2*~x1 + 3*x2 + 4*x3 >= 8
    // Cancel x1: degree -= 2*1 = 2 -> 3*x2 + 4*x3 >= 6
    assert_eq!(result.degree, 6);
    let coeff_map: std::collections::HashMap<i32, i64> =
        result.terms.iter().map(|&(c, l)| (l, c)).collect();
    assert_eq!(coeff_map.get(&2), Some(&3));
    assert_eq!(coeff_map.get(&3), Some(&4));
    assert!(!coeff_map.contains_key(&1)); // x1 cancelled
    assert!(!coeff_map.contains_key(&-1)); // ~x1 cancelled
}

#[test]
fn test_rule_generalized_resolution_sign_mismatch() {
    // Both constraints have x1 positively only: cannot resolve (no -x1 anywhere).
    let formula = PbFormula::new(2);
    let derived = vec![
        PbConstraint::new(vec![(1, 1), (1, 2)], 1),
        PbConstraint::new(vec![(1, 1), (1, 2)], 1),
    ];

    let err = verify_rule(
        &derived,
        &formula,
        &PbRule::GeneralizedResolution {
            left: 0,
            right: 1,
            var: 1,
        },
    )
    .unwrap_err();
    assert!(
        matches!(err, PbError::ResolutionSignMismatch { .. }),
        "expected sign mismatch error, got: {err:?}"
    );
}

// ============================================================
// Full proof verification
// ============================================================

#[test]
fn test_verify_pb_proof_simple_contradiction() {
    // x1 >= 1 and ~x1 >= 1 -> add -> 0 >= 2 (contradiction after cancel)
    // Actually: x1 + ~x1 >= 2, which means 1 >= 2, contradiction.
    // Let's do it step by step:
    // Step 0: Input x1 >= 1
    // Step 1: Input ~x1 >= 1
    // Step 2: Add 0,1 -> x1 + ~x1 >= 2
    // But we need to get to 0 >= k. Use resolution instead:
    // Or: multiply x1>=1 by 1 and ~x1>=1 by 1, resolve on x1.

    let mut formula = PbFormula::new(1);
    formula.add_constraint(PbConstraint::new(vec![(1, 1)], 1)); // x1 >= 1
    formula.add_constraint(PbConstraint::new(vec![(1, -1)], 1)); // ~x1 >= 1

    let proof = vec![
        PbRule::Input(0), // x1 >= 1
        PbRule::Input(1), // ~x1 >= 1
        PbRule::GeneralizedResolution {
            left: 0,
            right: 1,
            var: 1,
        }, // resolvent
    ];

    let result = verify_pb_proof(&formula, &proof);
    // After resolution: multiply L by 1, R by 1, add, cancel x1.
    // degree = 1 + 1 - 1*1 = 1. No terms left. 0 >= 1 => contradiction.
    result.expect("proof should verify as contradiction");
}

#[test]
fn test_verify_pb_proof_no_contradiction_fails() {
    let mut formula = PbFormula::new(1);
    formula.add_constraint(PbConstraint::new(vec![(1, 1)], 1));

    let proof = vec![PbRule::Input(0)]; // Just load an input, no contradiction.
    let err = verify_pb_proof(&formula, &proof).unwrap_err();
    assert!(matches!(err, PbError::NoContradiction));
}

#[test]
fn test_verify_pb_proof_index_out_of_bounds() {
    let formula = PbFormula::new(1);
    let proof = vec![PbRule::Input(5)]; // No constraint at index 5.
    let err = verify_pb_proof(&formula, &proof).unwrap_err();
    assert!(matches!(err, PbError::IndexOutOfBounds { .. }));
}

// ============================================================
// VeriPB proof compilation and verification
// ============================================================

#[test]
fn test_veripb_proof_verify() {
    let mut formula = PbFormula::new(1);
    formula.add_constraint(PbConstraint::new(vec![(1, 1)], 1));
    formula.add_constraint(PbConstraint::new(vec![(1, -1)], 1));

    let mut proof = VeriPbProof::new(formula);

    // Derive constraints.
    proof.add_step(VeriPbStep::PolynomialAddition {
        result: PbConstraint::new(vec![(1, 1)], 1),
        rule: PbRule::Input(0),
    });
    proof.add_step(VeriPbStep::PolynomialAddition {
        result: PbConstraint::new(vec![(1, -1)], 1),
        rule: PbRule::Input(1),
    });
    proof.add_step(VeriPbStep::PolynomialAddition {
        result: PbConstraint::new(vec![], 1), // 0 >= 1
        rule: PbRule::GeneralizedResolution {
            left: 0,
            right: 1,
            var: 1,
        },
    });
    proof.add_step(VeriPbStep::Conclude);

    proof.verify().expect("VeriPB proof should verify");
}

#[test]
fn test_veripb_format_output() {
    let mut formula = PbFormula::new(2);
    formula.add_constraint(PbConstraint::new(vec![(1, 1), (1, 2)], 1));

    let mut proof = VeriPbProof::new(formula);
    proof.add_step(VeriPbStep::PolynomialAddition {
        result: PbConstraint::new(vec![(1, 1), (1, 2)], 1),
        rule: PbRule::Input(0),
    });

    let output = proof.to_veripb_format();
    assert!(output.contains("pseudo-Boolean proof version 2.0"));
    assert!(output.contains("f 1"));
    assert!(output.contains("p 1 x1 1 x2 >= 1 ;"));
    assert!(output.contains("end pseudo-Boolean proof"));
}

#[test]
fn test_veripb_certificate_size() {
    let mut formula = PbFormula::new(1);
    formula.add_constraint(PbConstraint::new(vec![(1, 1)], 1));

    let proof = VeriPbProof::new(formula);
    let size = proof.certificate_size();
    assert!(size > 0);
}

#[test]
fn test_veripb_delete_then_resolve_before_delete() {
    // Derive the contradiction BEFORE the delete, then delete, then conclude.
    let mut formula = PbFormula::new(1);
    formula.add_constraint(PbConstraint::new(vec![(1, 1)], 1));
    formula.add_constraint(PbConstraint::new(vec![(1, -1)], 1));

    let mut proof = VeriPbProof::new(formula);
    proof.add_step(VeriPbStep::PolynomialAddition {
        result: PbConstraint::new(vec![(1, 1)], 1),
        rule: PbRule::Input(0),
    });
    proof.add_step(VeriPbStep::PolynomialAddition {
        result: PbConstraint::new(vec![(1, -1)], 1),
        rule: PbRule::Input(1),
    });
    // Resolve BEFORE delete — both constraints are live.
    proof.add_step(VeriPbStep::PolynomialAddition {
        result: PbConstraint::new(vec![], 1),
        rule: PbRule::GeneralizedResolution {
            left: 0,
            right: 1,
            var: 1,
        },
    });
    proof.add_step(VeriPbStep::Delete { id: 0 }); // Delete after derivation.
    proof.add_step(VeriPbStep::Conclude);

    proof
        .verify()
        .expect("VeriPB proof with delete after resolve should verify");
}

#[test]
fn test_soundness_veripb_delete_then_reference_rejected() {
    // SOUNDNESS BUG: After deleting constraint 0, referencing it in a
    // subsequent derivation must be rejected. Previously, delete was
    // a no-op that never invalidated the constraint.
    let mut formula = PbFormula::new(1);
    formula.add_constraint(PbConstraint::new(vec![(1, 1)], 1));
    formula.add_constraint(PbConstraint::new(vec![(1, -1)], 1));

    let mut proof = VeriPbProof::new(formula);
    proof.add_step(VeriPbStep::PolynomialAddition {
        result: PbConstraint::new(vec![(1, 1)], 1),
        rule: PbRule::Input(0),
    });
    proof.add_step(VeriPbStep::PolynomialAddition {
        result: PbConstraint::new(vec![(1, -1)], 1),
        rule: PbRule::Input(1),
    });
    proof.add_step(VeriPbStep::Delete { id: 0 }); // Delete constraint 0.
                                                  // Now try to use deleted constraint 0 in a derivation.
    proof.add_step(VeriPbStep::PolynomialAddition {
        result: PbConstraint::new(vec![], 1),
        rule: PbRule::GeneralizedResolution {
            left: 0, // DELETED — should fail
            right: 1,
            var: 1,
        },
    });
    proof.add_step(VeriPbStep::Conclude);

    let err = proof.verify().unwrap_err();
    assert!(
        matches!(err, PbError::IndexOutOfBounds { index: 0, .. }),
        "SOUNDNESS BUG: referencing deleted constraint was not rejected, got: {err}"
    );
}

#[test]
fn test_veripb_delete_out_of_bounds() {
    let formula = PbFormula::new(1);
    let mut proof = VeriPbProof::new(formula);
    proof.add_step(VeriPbStep::Delete { id: 99 });

    let err = proof.verify().unwrap_err();
    assert!(matches!(err, PbError::IndexOutOfBounds { .. }));
}

// ============================================================
// Cutting planes to VeriPB conversion
// ============================================================

#[test]
fn test_cutting_planes_to_veripb_simple() {
    // Build a simple CP proof: x >= 1, -x >= 0, add -> 0 >= 1.
    let mut cp = CuttingPlanesProof::new();
    let a = cp.add_input(CpInequality::new(vec![1], 1));
    let b = cp.add_input(CpInequality::new(vec![-1], 0));
    let _c = cp.add(a, b).expect("add");
    assert!(cp.verify());

    // Create matching PB formula.
    let mut formula = PbFormula::new(1);
    formula.add_constraint(PbConstraint::new(vec![(1, 1)], 1)); // x1 >= 1
    formula.add_constraint(PbConstraint::new(vec![(-1, 1)], 0)); // -x1 >= 0

    let veripb = cutting_planes_to_veripb(&cp, &formula).expect("conversion should succeed");
    assert!(veripb.steps.len() >= 3); // 2 inputs + 1 addition + conclude
}

// ============================================================
// Contradiction detection
// ============================================================

#[test]
fn test_pb_constraint_is_contradiction() {
    // 0 >= 1 is a contradiction.
    let c = PbConstraint::new(vec![], 1);
    assert!(c.is_contradiction());

    // 0 >= 0 is trivially satisfied.
    let c = PbConstraint::new(vec![], 0);
    assert!(!c.is_contradiction());

    // x1 >= 2 with coeff 1: max sum is 1 < 2.
    let c = PbConstraint::new(vec![(1, 1)], 2);
    assert!(c.is_contradiction());

    // x1 + x2 >= 2: max sum is 2 >= 2.
    let c = PbConstraint::new(vec![(1, 1), (1, 2)], 2);
    assert!(!c.is_contradiction());
}

// ============================================================
// Max variable
// ============================================================

#[test]
fn test_pb_constraint_max_var() {
    let c = PbConstraint::new(vec![(1, 3), (2, -5), (3, 1)], 1);
    assert_eq!(c.max_var(), 5);

    let c = PbConstraint::new(vec![], 0);
    assert_eq!(c.max_var(), 0);
}

// ============================================================
// Edge cases
// ============================================================

#[test]
fn test_pb_constraint_empty() {
    let c = PbConstraint::new(vec![], 0);
    assert!(!c.is_clause());
    assert!(!c.is_cardinality());
    assert!(c.to_clause().is_none()); // degree != 1
    assert!(!c.is_contradiction());
}

#[test]
fn test_pb_constraint_single_term() {
    let c = PbConstraint::new(vec![(1, 1)], 1);
    assert!(c.is_clause());
    assert_eq!(c.to_clause(), Some(vec![1]));
}

#[test]
fn test_evaluate_empty_assignment() {
    let c = PbConstraint::new(vec![(1, 1), (1, 2)], 1);
    let assignment: Vec<Option<bool>> = vec![None, None, None];
    // All unassigned: max_remaining = 2 >= 1, but sum = 0 < 1.
    assert_eq!(c.evaluate(&assignment), None);
}

#[test]
fn test_propagate_with_negated_literals() {
    // ~x1 + ~x2 >= 2 (both must be negated)
    let c = PbConstraint::new(vec![(1, -1), (1, -2)], 2);
    let assignment: Vec<Option<bool>> = vec![None, None, None];

    let forced = c.propagate(&assignment);
    // Both ~x1 and ~x2 are forced (without either, max=1 < 2).
    assert!(forced.contains(&-1));
    assert!(forced.contains(&-2));
}

#[test]
fn test_division_rule_on_php_encoding() {
    // PHP(2,1) produces constraints where division is useful.
    // Suppose after some derivation we have: 2*x1 + 2*x2 >= 3
    // Divide by 2: ceil(2/2)*x1 + ceil(2/2)*x2 >= ceil(3/2) = x1 + x2 >= 2
    let formula = PbFormula::new(2);
    let derived = vec![PbConstraint::new(vec![(2, 1), (2, 2)], 3)];

    let result = verify_rule(
        &derived,
        &formula,
        &PbRule::Division {
            constraint: 0,
            divisor: 2,
        },
    )
    .expect("division should succeed");

    assert_eq!(result.terms[0], (1, 1));
    assert_eq!(result.terms[1], (1, 2));
    assert_eq!(result.degree, 2);
}

// ============================================================
// Adversarial soundness tests (audit findings)
// ============================================================

#[test]
fn test_mixed_polarity_left_simplifies_and_resolves() {
    // Mixed polarity in left constraint is now handled by simplification.
    //
    // left = 2*x1 + 3*~x1 + 1*x2 >= 4 (x1 in both polarities)
    // right = 1*~x1 + 1*x3 >= 1
    //
    // Simplify left: 2*x1 + 3*~x1 = (3-2)*~x1 + 2 absorbed into degree
    //   -> 1*~x1 + 1*x2 >= 4 - 2 = 2
    // But wait: after simplification left has ~x1 (negative), not +x1.
    // So resolution expects left to have +v and right to have -v.
    // After simplification, left has ~x1 and right has ~x1, so resolution
    // should fail with sign mismatch (both have -v, neither has +v).
    //
    // Use a different example where simplification yields a valid resolvent:
    // left = 5*x1 + 2*~x1 + 3*x2 >= 6 (mixed polarity on x1)
    // After simplification: 5*x1 + 2*~x1 = (5-2)*x1 + 2 -> degree -= 2
    //   -> 3*x1 + 3*x2 >= 4
    // right = 2*~x1 + 1*x3 >= 2
    //
    // Now resolve on x1: c_l = 3, c_r = 2
    // Scale left by 2: 6*x1 + 6*x2 >= 8
    // Scale right by 3: 6*~x1 + 3*x3 >= 6
    // Add: 6*x1 + 6*~x1 + 6*x2 + 3*x3 >= 14
    // Cancel: degree -= 6 -> 6*x2 + 3*x3 >= 8
    let formula = PbFormula::new(3);
    let derived = vec![
        PbConstraint::new(vec![(5, 1), (2, -1), (3, 2)], 6), // left: mixed polarity on x1
        PbConstraint::new(vec![(2, -1), (1, 3)], 2),         // right: -x1
    ];

    let result = verify_rule(
        &derived,
        &formula,
        &PbRule::GeneralizedResolution {
            left: 0,
            right: 1,
            var: 1,
        },
    )
    .expect("mixed polarity should be simplified and resolved");

    assert_eq!(result.degree, 8);
    let coeff_map: std::collections::HashMap<i32, i64> =
        result.terms.iter().map(|&(c, l)| (l, c)).collect();
    assert_eq!(coeff_map.get(&2), Some(&6));
    assert_eq!(coeff_map.get(&3), Some(&3));
    assert!(!coeff_map.contains_key(&1)); // x1 cancelled
    assert!(!coeff_map.contains_key(&-1)); // ~x1 cancelled

    // Verify soundness: check all 8 assignments for 3 variables.
    for x1 in [false, true] {
        for x2 in [false, true] {
            for x3 in [false, true] {
                // Check original left: 5*x1 + 2*~x1 + 3*x2 >= 6
                let left_sum =
                    if x1 { 5 } else { 0 } + if !x1 { 2 } else { 0 } + if x2 { 3 } else { 0 };
                let left_sat = left_sum >= 6;

                // Check original right: 2*~x1 + 1*x3 >= 2
                let right_sum = if !x1 { 2 } else { 0 } + if x3 { 1 } else { 0 };
                let right_sat = right_sum >= 2;

                // Check result: 6*x2 + 3*x3 >= 8
                let result_sum = if x2 { 6 } else { 0 } + if x3 { 3 } else { 0 };
                let result_sat = result_sum >= 8;

                // Soundness: if both premises satisfied, conclusion must be satisfied.
                if left_sat && right_sat {
                    assert!(
                        result_sat,
                        "UNSOUND: x1={x1}, x2={x2}, x3={x3}: premises satisfied but result {result_sum} < 8"
                    );
                }
            }
        }
    }
}

#[test]
fn test_mixed_polarity_right_simplifies_and_resolves() {
    // Mixed polarity in right constraint is now handled by simplification.
    //
    // left = 3*x1 + 2*x2 >= 3 (only +x1)
    // right = 4*~x1 + 1*x1 + 2*x3 >= 3 (mixed polarity on x1)
    //
    // Simplify right: 4*~x1 + 1*x1 = (4-1)*~x1 + 1 -> degree -= 1
    //   -> 3*~x1 + 2*x3 >= 2
    //
    // Now resolve on x1: c_l = 3 (left's x1), c_r = 3 (right's ~x1)
    // Scale left by 3: 9*x1 + 6*x2 >= 9
    // Scale right by 3: 9*~x1 + 6*x3 >= 6
    // Add: 9*x1 + 9*~x1 + 6*x2 + 6*x3 >= 15
    // Cancel: degree -= 9 -> 6*x2 + 6*x3 >= 6
    let formula = PbFormula::new(3);
    let derived = vec![
        PbConstraint::new(vec![(3, 1), (2, 2)], 3), // left: +x1
        PbConstraint::new(vec![(4, -1), (1, 1), (2, 3)], 3), // right: mixed polarity on x1
    ];

    let result = verify_rule(
        &derived,
        &formula,
        &PbRule::GeneralizedResolution {
            left: 0,
            right: 1,
            var: 1,
        },
    )
    .expect("mixed polarity in right should be simplified and resolved");

    assert_eq!(result.degree, 6);
    let coeff_map: std::collections::HashMap<i32, i64> =
        result.terms.iter().map(|&(c, l)| (l, c)).collect();
    assert_eq!(coeff_map.get(&2), Some(&6));
    assert_eq!(coeff_map.get(&3), Some(&6));
    assert!(!coeff_map.contains_key(&1));
    assert!(!coeff_map.contains_key(&-1));

    // Verify soundness: check all 8 assignments.
    for x1 in [false, true] {
        for x2 in [false, true] {
            for x3 in [false, true] {
                let left_sum = if x1 { 3 } else { 0 } + if x2 { 2 } else { 0 };
                let left_sat = left_sum >= 3;

                let right_sum =
                    if !x1 { 4 } else { 0 } + if x1 { 1 } else { 0 } + if x3 { 2 } else { 0 };
                let right_sat = right_sum >= 3;

                let result_sum = if x2 { 6 } else { 0 } + if x3 { 6 } else { 0 };
                let result_sat = result_sum >= 6;

                if left_sat && right_sat {
                    assert!(
                        result_sat,
                        "UNSOUND: x1={x1}, x2={x2}, x3={x3}: premises satisfied but result {result_sum} < 6"
                    );
                }
            }
        }
    }
}

#[test]
fn test_mixed_polarity_both_sides_simplifies_and_resolves() {
    // Both constraints have mixed polarity on x1.
    //
    // left = 4*x1 + 1*~x1 + 2*x2 >= 3 (mixed polarity on x1)
    // right = 3*~x1 + 1*x1 + 1*x3 >= 2 (mixed polarity on x1)
    //
    // Simplify left: 4*x1 + 1*~x1 = (4-1)*x1 + 1 -> degree -= 1
    //   -> 3*x1 + 2*x2 >= 2
    // Simplify right: 3*~x1 + 1*x1 = (3-1)*~x1 + 1 -> degree -= 1
    //   -> 2*~x1 + 1*x3 >= 1
    //
    // Resolve on x1: c_l = 3, c_r = 2
    // Scale left by 2: 6*x1 + 4*x2 >= 4
    // Scale right by 3: 6*~x1 + 3*x3 >= 3
    // Add: 6*x1 + 6*~x1 + 4*x2 + 3*x3 >= 7
    // Cancel: degree -= 6 -> 4*x2 + 3*x3 >= 1
    let formula = PbFormula::new(3);
    let derived = vec![
        PbConstraint::new(vec![(4, 1), (1, -1), (2, 2)], 3), // left: mixed
        PbConstraint::new(vec![(3, -1), (1, 1), (1, 3)], 2), // right: mixed
    ];

    let result = verify_rule(
        &derived,
        &formula,
        &PbRule::GeneralizedResolution {
            left: 0,
            right: 1,
            var: 1,
        },
    )
    .expect("both-sides mixed polarity should be simplified and resolved");

    assert_eq!(result.degree, 1);
    let coeff_map: std::collections::HashMap<i32, i64> =
        result.terms.iter().map(|&(c, l)| (l, c)).collect();
    assert_eq!(coeff_map.get(&2), Some(&4));
    assert_eq!(coeff_map.get(&3), Some(&3));
    assert!(!coeff_map.contains_key(&1));
    assert!(!coeff_map.contains_key(&-1));

    // Verify soundness.
    for x1 in [false, true] {
        for x2 in [false, true] {
            for x3 in [false, true] {
                let left_sum =
                    if x1 { 4 } else { 0 } + if !x1 { 1 } else { 0 } + if x2 { 2 } else { 0 };
                let left_sat = left_sum >= 3;

                let right_sum =
                    if !x1 { 3 } else { 0 } + if x1 { 1 } else { 0 } + if x3 { 1 } else { 0 };
                let right_sat = right_sum >= 2;

                let result_sum = if x2 { 4 } else { 0 } + if x3 { 3 } else { 0 };
                let result_sat = result_sum >= 1;

                if left_sat && right_sat {
                    assert!(
                        result_sat,
                        "UNSOUND: x1={x1}, x2={x2}, x3={x3}: premises satisfied but result {result_sum} < 1"
                    );
                }
            }
        }
    }
}

#[test]
fn test_mixed_polarity_simplifies_to_no_var_gives_sign_mismatch() {
    // Edge case: after simplification, the variable is completely eliminated
    // from both constraints, so resolution cannot find the required signs.
    //
    // left = 3*x1 + 3*~x1 + 1*x2 >= 4 (equal coefficients: net = 0)
    // After simplification: 3*x1 + 3*~x1 = 0 + 3 -> degree -= 3
    //   -> 1*x2 >= 1
    // right = 2*~x1 + 1*x3 >= 2
    //
    // left has no x1 or ~x1 after simplification -> sign mismatch.
    let formula = PbFormula::new(3);
    let derived = vec![
        PbConstraint::new(vec![(3, 1), (3, -1), (1, 2)], 4),
        PbConstraint::new(vec![(2, -1), (1, 3)], 2),
    ];

    let err = verify_rule(
        &derived,
        &formula,
        &PbRule::GeneralizedResolution {
            left: 0,
            right: 1,
            var: 1,
        },
    )
    .unwrap_err();

    assert!(
        matches!(err, PbError::ResolutionSignMismatch { var: 1, .. }),
        "expected sign mismatch when mixed polarity eliminates var, got: {err:?}"
    );
}

#[test]
fn test_generalized_resolution_single_polarity_still_works() {
    // Ensure the fix does not break legitimate single-polarity resolution.
    // left: 3*x1 + 2*x2 >= 3 (only +x1)
    // right: 2*~x1 + 1*x3 >= 2 (only -x1)
    let formula = PbFormula::new(3);
    let derived = vec![
        PbConstraint::new(vec![(3, 1), (2, 2)], 3),
        PbConstraint::new(vec![(2, -1), (1, 3)], 2),
    ];

    let result = verify_rule(
        &derived,
        &formula,
        &PbRule::GeneralizedResolution {
            left: 0,
            right: 1,
            var: 1,
        },
    )
    .expect("single-polarity resolution should still work");

    // Scale left by c_r=2: 6*x1 + 4*x2 >= 6
    // Scale right by c_l=3: 6*~x1 + 3*x3 >= 6
    // Add: 6*x1 + 6*~x1 + 4*x2 + 3*x3 >= 12
    // Cancel: degree -= 6 -> 4*x2 + 3*x3 >= 6
    assert_eq!(result.degree, 6);
    let coeff_map: std::collections::HashMap<i32, i64> =
        result.terms.iter().map(|&(c, l)| (l, c)).collect();
    assert_eq!(coeff_map.get(&2), Some(&4));
    assert_eq!(coeff_map.get(&3), Some(&3));
    assert!(!coeff_map.contains_key(&1));
    assert!(!coeff_map.contains_key(&-1));
}

// ============================================================
// Integration: OPB parse -> normalize -> prove -> export certificate
// ============================================================

#[test]
fn test_integration_opb_parse_normalize_prove_certificate() {
    // Parse an OPB formula: x1 >= 1 AND ~x1 >= 1 (contradictory).
    let opb_input = "\
* #variable= 1 #constraint= 2
+1 x1 >= 1 ;
+1 ~x1 >= 1 ;
";
    let formula = parse_opb(opb_input).expect("should parse OPB");
    assert_eq!(formula.num_vars, 1);
    assert_eq!(formula.constraints.len(), 2);

    // Normalize constraints.
    let normalized = simplify_formula(&formula);
    assert_eq!(normalized.constraints.len(), 2); // Neither is a tautology.

    // Build a proof: resolve x1 >= 1 and ~x1 >= 1 to derive 0 >= 1.
    let mut proof = VeriPbProof::new(normalized);
    proof.add_step(VeriPbStep::PolynomialAddition {
        result: PbConstraint::new(vec![(1, 1)], 1),
        rule: PbRule::Input(0),
    });
    proof.add_step(VeriPbStep::PolynomialAddition {
        result: PbConstraint::new(vec![(1, -1)], 1),
        rule: PbRule::Input(1),
    });
    proof.add_step(VeriPbStep::PolynomialAddition {
        result: PbConstraint::new(vec![], 1),
        rule: PbRule::GeneralizedResolution {
            left: 0,
            right: 1,
            var: 1,
        },
    });
    proof.add_step(VeriPbStep::Conclude);

    proof.verify().expect("proof should verify");

    // Export certificate.
    let cert = export_certificate(&proof);
    assert!(cert.verified);
    assert!(!cert.formula_hash.is_empty());
    assert_eq!(cert.stats.formula_size, 2);
    assert!(cert.proof_text.contains("blake3:"));
}

#[test]
fn test_integration_cnf_to_pb_normalize_roundtrip() {
    // Start with CNF, convert to PB, normalize, convert back.
    let clauses = vec![vec![1, 2, 3], vec![-1, 2], vec![1, -3]];

    let pb_formula = cnf_to_pb(&clauses);
    assert!(is_cnf_representable(&pb_formula));

    // Normalize all constraints.
    let simplified = simplify_formula(&pb_formula);
    // Clause constraints normalize trivially (no duplicates, no negation pairs).
    assert_eq!(simplified.constraints.len(), 3);

    // Convert back.
    let recovered = pb_to_cnf(&simplified).expect("should convert back to CNF");
    assert_eq!(recovered.len(), 3);
}

#[test]
fn test_integration_opb_roundtrip_with_normalization() {
    let opb_input = "\
* #variable= 3 #constraint= 3
+1 x1 +2 x2 +3 x3 >= 4 ;
+1 x1 +1 x2 >= 1 ;
+1 x3 >= 0 ;
";
    let formula = parse_opb(opb_input).expect("should parse");

    // Simplify: the last constraint (x3 >= 0) is a tautology and should be removed.
    let simplified = simplify_formula(&formula);
    assert_eq!(simplified.constraints.len(), 2);

    // Write back to OPB.
    let output = write_opb(&simplified);
    assert!(output.contains("#constraint= 2"));

    // Re-parse and verify equivalence.
    let reparsed = parse_opb(&output).expect("should re-parse");
    assert_eq!(reparsed.constraints.len(), 2);
}

#[test]
fn test_integration_cnf_bridge_prove_unsat() {
    // CNF: (x1) AND (~x1) — trivially UNSAT.
    let clauses = vec![vec![1], vec![-1]];
    let formula = cnf_to_pb(&clauses);

    // Prove UNSAT via PB proof.
    let proof_steps = vec![
        PbRule::Input(0),
        PbRule::Input(1),
        PbRule::GeneralizedResolution {
            left: 0,
            right: 1,
            var: 1,
        },
    ];

    verify_pb_proof(&formula, &proof_steps).expect("CNF UNSAT proof should verify");
}

#[test]
fn test_integration_normalize_saturate_certificate_pipeline() {
    // 10*x1 + 10*x2 >= 3
    let c = PbConstraint::new(vec![(10, 1), (10, 2)], 3);
    let normalized = normalize(&c);
    let saturated = saturate(&normalized);

    // After saturation: 3*x1 + 3*x2 >= 3
    assert_eq!(saturated.degree, 3);
    let coeff_map: std::collections::HashMap<i32, i64> =
        saturated.terms.iter().map(|&(c, l)| (l, c)).collect();
    assert_eq!(coeff_map.get(&1), Some(&3));
    assert_eq!(coeff_map.get(&2), Some(&3));

    // Build a formula and hash it for certificate.
    let mut formula = PbFormula::new(2);
    formula.add_constraint(saturated);
    let hash = hash_formula(&formula);
    assert!(!hash.is_empty());
    assert_eq!(hash.len(), 64); // blake3 hex is 64 chars
}

#[test]
fn test_integration_export_veripb_with_hash_parseable() {
    // Build a small proof, export, and verify the hash header format.
    let mut formula = PbFormula::new(2);
    formula.add_constraint(PbConstraint::new(vec![(1, 1), (1, 2)], 1));
    formula.add_constraint(PbConstraint::new(vec![(1, -1), (1, -2)], 1));

    let proof = VeriPbProof::new(formula);
    let text = export_veripb(&proof);

    // Verify the format of the hash line.
    let first_line = text.lines().next().expect("should have first line");
    assert!(first_line.starts_with("* formula-hash: blake3:"));
    let hash_value = first_line.strip_prefix("* formula-hash: blake3:").unwrap();
    assert_eq!(hash_value.len(), 64);
    assert!(hash_value.chars().all(|c| c.is_ascii_hexdigit()));
}
