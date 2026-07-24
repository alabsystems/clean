// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the Cutting Planes separation proof module (`separations_cp`).
//!
//! Covers: SepCpStep (derive traits), verify_cp_derivation (valid/invalid proofs,
//! edge cases), cp_proof_of_php (correctness, polynomial size), php_cp_axioms
//! (structure, variable layout).

use super::cutting_planes::CpInequality;
use super::separations_cp::*;

// ===== SepCpStep derive traits =====

#[test]
fn test_sep_cp_step_debug_all_variants() {
    let variants: Vec<SepCpStep> = vec![
        SepCpStep::Addition(0, 1),
        SepCpStep::Multiplication(0, 5),
        SepCpStep::Division(0, 3),
        SepCpStep::Weakening(0, 2),
        SepCpStep::BooleanAxiom(7),
    ];
    let names = [
        "Addition",
        "Multiplication",
        "Division",
        "Weakening",
        "BooleanAxiom",
    ];
    for (step, name) in variants.iter().zip(names.iter()) {
        let dbg = format!("{step:?}");
        assert!(dbg.contains(name), "expected {name} in {dbg}");
    }
}

#[test]
fn test_sep_cp_step_clone() {
    let step = SepCpStep::Multiplication(3, 42);
    let cloned = step.clone();
    assert_eq!(step, cloned);
}

#[test]
fn test_sep_cp_step_partial_eq() {
    assert_eq!(SepCpStep::Addition(0, 1), SepCpStep::Addition(0, 1));
    assert_ne!(SepCpStep::Addition(0, 1), SepCpStep::Addition(1, 0));
    assert_ne!(SepCpStep::Addition(0, 1), SepCpStep::Multiplication(0, 1));
}

#[test]
fn test_sep_cp_step_eq_transitivity() {
    let a = SepCpStep::Division(2, 7);
    let b = a.clone();
    let c = b.clone();
    assert_eq!(a, c);
}

// ===== verify_cp_derivation -- valid proofs =====

#[test]
fn test_verify_simple_contradiction() {
    // x >= 1 and -x >= 0 => add => 0 >= 1
    let axioms = vec![
        CpInequality::new(vec![1], 1),
        CpInequality::new(vec![-1], 0),
    ];
    let steps = vec![SepCpStep::Addition(0, 1)];
    assert!(verify_cp_derivation(&axioms, &steps));
}

#[test]
fn test_verify_php_0_already_contradiction() {
    // PHP(1,0): axiom is [] >= 1, i.e. 0 >= 1. Empty steps.
    let axioms = php_cp_axioms(0);
    let steps = cp_proof_of_php(0);
    assert!(steps.is_empty());
    assert!(verify_cp_derivation(&axioms, &steps));
}

#[test]
fn test_verify_php_2_1() {
    let axioms = php_cp_axioms(1);
    let steps = cp_proof_of_php(1);
    assert!(verify_cp_derivation(&axioms, &steps));
}

#[test]
fn test_verify_php_3_2() {
    let axioms = php_cp_axioms(2);
    let steps = cp_proof_of_php(2);
    assert!(verify_cp_derivation(&axioms, &steps));
}

#[test]
fn test_verify_php_4_3() {
    let axioms = php_cp_axioms(3);
    let steps = cp_proof_of_php(3);
    assert!(verify_cp_derivation(&axioms, &steps));
}

#[test]
fn test_verify_php_5_4() {
    let axioms = php_cp_axioms(4);
    let steps = cp_proof_of_php(4);
    assert!(verify_cp_derivation(&axioms, &steps));
}

#[test]
fn test_verify_multiplication_step() {
    // x >= 1, multiply by 2 => 2x >= 2, then add -2x >= -1 => 0 >= 1
    let axioms = vec![
        CpInequality::new(vec![1], 1),
        CpInequality::new(vec![-2], -1),
    ];
    let steps = vec![SepCpStep::Multiplication(0, 2), SepCpStep::Addition(2, 1)];
    assert!(verify_cp_derivation(&axioms, &steps));
}

#[test]
fn test_verify_division_step_ceiling() {
    // 2x >= 3, divide by 2 => x >= 2, then add -x >= -1 => 0 >= 1
    let axioms = vec![
        CpInequality::new(vec![2], 3),
        CpInequality::new(vec![-1], -1),
    ];
    let steps = vec![SepCpStep::Division(0, 2), SepCpStep::Addition(2, 1)];
    assert!(verify_cp_derivation(&axioms, &steps));
}

#[test]
fn test_verify_weakening_step() {
    // x + y >= 1, weaken y => x >= 1, then add -x >= 0 => 0 >= 1
    let axioms = vec![
        CpInequality::new(vec![1, 1], 1),
        CpInequality::new(vec![-1, 0], 0),
    ];
    let steps = vec![SepCpStep::Weakening(0, 1), SepCpStep::Addition(2, 1)];
    assert!(verify_cp_derivation(&axioms, &steps));
}

#[test]
fn test_verify_boolean_axiom_step() {
    // BooleanAxiom(0) creates x_0 >= 0.
    // -x_0 >= 1 + x_0 >= 0 => 0 >= 1.
    let axioms = vec![CpInequality::new(vec![-1], 1)];
    let steps = vec![SepCpStep::BooleanAxiom(0), SepCpStep::Addition(0, 1)];
    assert!(verify_cp_derivation(&axioms, &steps));
}

#[test]
fn test_verify_multi_step_chain() {
    // x0>=1, x1>=1, x2>=1, -x0-x1-x2>=-2 => sum all => 0>=1
    let axioms = vec![
        CpInequality::new(vec![1, 0, 0], 1),
        CpInequality::new(vec![0, 1, 0], 1),
        CpInequality::new(vec![0, 0, 1], 1),
        CpInequality::new(vec![-1, -1, -1], -2),
    ];
    let steps = vec![
        SepCpStep::Addition(0, 1),
        SepCpStep::Addition(4, 2),
        SepCpStep::Addition(5, 3),
    ];
    assert!(verify_cp_derivation(&axioms, &steps));
}

// ===== verify_cp_derivation -- invalid proofs =====

#[test]
fn test_verify_empty_steps_no_contradiction() {
    let axioms = vec![CpInequality::new(vec![1], 1)];
    assert!(!verify_cp_derivation(&axioms, &[]));
}

#[test]
fn test_verify_empty_axioms_empty_steps() {
    assert!(!verify_cp_derivation(&[], &[]));
}

#[test]
fn test_verify_invalid_addition_index() {
    let axioms = vec![CpInequality::new(vec![1], 1)];
    assert!(!verify_cp_derivation(
        &axioms,
        &[SepCpStep::Addition(0, 99)]
    ));
}

#[test]
fn test_verify_invalid_addition_both_indices() {
    let axioms = vec![CpInequality::new(vec![1], 1)];
    assert!(!verify_cp_derivation(
        &axioms,
        &[SepCpStep::Addition(5, 10)]
    ));
}

#[test]
fn test_verify_multiplication_by_zero() {
    let axioms = vec![CpInequality::new(vec![1], 1)];
    assert!(!verify_cp_derivation(
        &axioms,
        &[SepCpStep::Multiplication(0, 0)]
    ));
}

#[test]
fn test_verify_multiplication_by_negative() {
    let axioms = vec![CpInequality::new(vec![1], 1)];
    assert!(!verify_cp_derivation(
        &axioms,
        &[SepCpStep::Multiplication(0, -3)]
    ));
}

#[test]
fn test_verify_division_by_zero() {
    let axioms = vec![CpInequality::new(vec![2], 4)];
    assert!(!verify_cp_derivation(&axioms, &[SepCpStep::Division(0, 0)]));
}

#[test]
fn test_verify_division_by_negative() {
    let axioms = vec![CpInequality::new(vec![2], 4)];
    assert!(!verify_cp_derivation(
        &axioms,
        &[SepCpStep::Division(0, -2)]
    ));
}

#[test]
fn test_verify_steps_no_contradiction_reached() {
    let axioms = vec![CpInequality::new(vec![1], 1), CpInequality::new(vec![1], 1)];
    assert!(!verify_cp_derivation(&axioms, &[SepCpStep::Addition(0, 1)]));
}

#[test]
fn test_verify_invalid_index_multiplication() {
    let axioms = vec![CpInequality::new(vec![1], 1)];
    assert!(!verify_cp_derivation(
        &axioms,
        &[SepCpStep::Multiplication(5, 2)]
    ));
}

#[test]
fn test_verify_invalid_index_division() {
    let axioms = vec![CpInequality::new(vec![1], 1)];
    assert!(!verify_cp_derivation(&axioms, &[SepCpStep::Division(5, 2)]));
}

#[test]
fn test_verify_invalid_index_weakening() {
    let axioms = vec![CpInequality::new(vec![1], 1)];
    assert!(!verify_cp_derivation(
        &axioms,
        &[SepCpStep::Weakening(5, 0)]
    ));
}

// ===== cp_proof_of_php correctness =====

#[test]
fn test_php_proof_n0_empty() {
    assert!(cp_proof_of_php(0).is_empty());
}

#[test]
fn test_php_proof_n1_nonempty() {
    assert!(!cp_proof_of_php(1).is_empty());
}

#[test]
fn test_php_proof_n1_through_n5_verify() {
    for n in 1..=5 {
        let axioms = php_cp_axioms(n);
        let steps = cp_proof_of_php(n);
        assert!(
            verify_cp_derivation(&axioms, &steps),
            "PHP({},{}) should verify",
            n + 1,
            n
        );
    }
}

#[test]
fn test_php_proof_polynomial_step_count() {
    // Proof sums (n+1)-1 pigeon constraints then n hole constraints = 2n steps.
    for n in 1..=8 {
        let steps = cp_proof_of_php(n);
        assert_eq!(steps.len(), 2 * n, "PHP({},{}) step count", n + 1, n);
    }
}

#[test]
fn test_php_proof_steps_are_all_additions() {
    for n in 1..=5 {
        for step in cp_proof_of_php(n) {
            match step {
                SepCpStep::Addition(_, _) => {}
                other => panic!("PHP({},{}) has non-Addition step: {other:?}", n + 1, n),
            }
        }
    }
}

#[test]
fn test_php_proof_n10_verifies() {
    let axioms = php_cp_axioms(10);
    let steps = cp_proof_of_php(10);
    assert!(verify_cp_derivation(&axioms, &steps));
}

#[test]
fn test_php_proof_step_count_grows_linearly() {
    // Step count = 2n, so ratio step_count/n should be constant ~2.
    let s5 = cp_proof_of_php(5).len();
    let s10 = cp_proof_of_php(10).len();
    let s20 = cp_proof_of_php(20).len();
    assert_eq!(s5 as f64 / 5.0, 2.0);
    assert_eq!(s10 as f64 / 10.0, 2.0);
    assert_eq!(s20 as f64 / 20.0, 2.0);
}

// ===== php_cp_axioms structure =====

#[test]
fn test_axioms_n0_single() {
    let axioms = php_cp_axioms(0);
    assert_eq!(axioms.len(), 1);
    assert!(axioms[0].coeffs.is_empty());
    assert_eq!(axioms[0].rhs, 1);
}

#[test]
fn test_axioms_n1_count() {
    assert_eq!(php_cp_axioms(1).len(), 3); // 2 pigeon + 1 hole
}

#[test]
fn test_axioms_n2_count() {
    assert_eq!(php_cp_axioms(2).len(), 5); // 3 pigeon + 2 hole
}

#[test]
fn test_axioms_n3_count() {
    assert_eq!(php_cp_axioms(3).len(), 7); // 4 pigeon + 3 hole
}

#[test]
fn test_axioms_count_formula() {
    for n in 1..=6 {
        assert_eq!(php_cp_axioms(n).len(), 2 * n + 1);
    }
}

#[test]
fn test_axioms_num_variables() {
    for n in 1..=5 {
        let axioms = php_cp_axioms(n);
        let expected_vars = (n + 1) * n;
        for ax in &axioms {
            assert_eq!(ax.coeffs.len(), expected_vars);
        }
    }
}

#[test]
fn test_axioms_pigeon_constraint_structure() {
    for n in 1..=4 {
        let axioms = php_cp_axioms(n);
        for (i, ax) in axioms.iter().enumerate().take(n + 1) {
            assert_eq!(ax.rhs, 1);
            let sum: i64 = ax.coeffs.iter().sum();
            assert_eq!(sum, n as i64, "pigeon {i} coeff sum for n={n}");
            let ones = ax.coeffs.iter().filter(|&&c| c == 1).count();
            assert_eq!(ones, n, "pigeon {i} should have {n} ones");
        }
    }
}

#[test]
fn test_axioms_hole_constraint_structure() {
    for n in 1..=4 {
        let axioms = php_cp_axioms(n);
        let pigeons = n + 1;
        for j in 0..n {
            let ax = &axioms[pigeons + j];
            assert_eq!(ax.rhs, -1);
            let sum: i64 = ax.coeffs.iter().sum();
            assert_eq!(sum, -(pigeons as i64));
            let neg_ones = ax.coeffs.iter().filter(|&&c| c == -1).count();
            assert_eq!(neg_ones, pigeons);
        }
    }
}

// ===== Edge cases =====

#[test]
fn test_verify_all_zero_coeffs_contradiction() {
    let axioms = vec![CpInequality::new(vec![0, 0, 0], 1)];
    assert!(verify_cp_derivation(&axioms, &[]));
}

#[test]
fn test_verify_empty_coeffs_contradiction() {
    let axioms = vec![CpInequality::new(vec![], 5)];
    assert!(verify_cp_derivation(&axioms, &[]));
}

#[test]
fn test_verify_large_coefficients() {
    let axioms = vec![
        CpInequality::new(vec![1_000_000], 1_000_000),
        CpInequality::new(vec![-1_000_000], -999_999),
    ];
    assert!(verify_cp_derivation(&axioms, &[SepCpStep::Addition(0, 1)]));
}

#[test]
fn test_verify_long_derivation_chain() {
    // 10x>=10 -> div2 -> div2 -> div2 -> div2 -> add(-x>=0) => 0>=1
    let axioms = vec![
        CpInequality::new(vec![10], 10),
        CpInequality::new(vec![-1], 0),
    ];
    let steps = vec![
        SepCpStep::Division(0, 2), // 5x >= 5
        SepCpStep::Division(2, 2), // 3x >= 3
        SepCpStep::Division(3, 2), // 2x >= 2
        SepCpStep::Division(4, 2), // x >= 1
        SepCpStep::Addition(5, 1), // 0 >= 1
    ];
    assert!(verify_cp_derivation(&axioms, &steps));
}

#[test]
fn test_verify_weakening_out_of_range_var() {
    // Weakening var index beyond coeffs length is a no-op.
    let axioms = vec![
        CpInequality::new(vec![1], 1),
        CpInequality::new(vec![-1], 0),
    ];
    let steps = vec![
        SepCpStep::Weakening(0, 5), // no-op: var 5 beyond length
        SepCpStep::Addition(2, 1),  // 0 >= 1
    ];
    assert!(verify_cp_derivation(&axioms, &steps));
}

#[test]
fn test_verify_boolean_axiom_high_var_index() {
    let axioms = vec![CpInequality::new(vec![], 1)];
    // BooleanAxiom(10) => x_10 >= 0, not a contradiction
    assert!(!verify_cp_derivation(
        &axioms,
        &[SepCpStep::BooleanAxiom(10)]
    ));
}

#[test]
fn test_verify_addition_different_lengths() {
    // [1] >= 1 + [-1, -1] >= 0 => [0, -1] >= 1. Not contradiction.
    let axioms = vec![
        CpInequality::new(vec![1], 1),
        CpInequality::new(vec![-1, -1], 0),
    ];
    assert!(!verify_cp_derivation(&axioms, &[SepCpStep::Addition(0, 1)]));
}

#[test]
fn test_verify_derived_index_reference() {
    // Use derived index in subsequent step.
    let axioms = vec![
        CpInequality::new(vec![1, 0], 1),
        CpInequality::new(vec![0, 1], 1),
    ];
    let steps = vec![
        SepCpStep::Addition(0, 1),       // idx 2: x+y >= 2
        SepCpStep::Multiplication(2, 1), // idx 3: x+y >= 2 (using derived idx)
    ];
    assert!(!verify_cp_derivation(&axioms, &steps));
}

#[test]
fn test_verify_zero_ge_zero_not_contradiction() {
    let axioms = vec![
        CpInequality::new(vec![1], 0),
        CpInequality::new(vec![-1], 0),
    ];
    assert!(!verify_cp_derivation(&axioms, &[SepCpStep::Addition(0, 1)]));
}

#[test]
fn test_verify_zero_ge_negative_not_contradiction() {
    let axioms = vec![
        CpInequality::new(vec![1], -1),
        CpInequality::new(vec![-1], -1),
    ];
    assert!(!verify_cp_derivation(&axioms, &[SepCpStep::Addition(0, 1)]));
}
