// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended mathverse support (modular and bitvector arithmetic)

use super::arithmetic::LinearExpr;
use super::mathverse_ext::*;

// =============================================================================
// Config tests
// =============================================================================

#[test]
fn test_mathverse_ext_default_config_values() {
    let cfg = MathverseExtConfig::default();
    assert!(cfg.enable_mod);
    assert!(cfg.enable_bv);
    assert_eq!(cfg.max_bv_width, 64);
    assert_eq!(cfg.mod_bound, 1u64 << 32);
}

#[test]
fn test_mathverse_ext_custom_config() {
    let cfg = MathverseExtConfig {
        enable_mod: false,
        enable_bv: true,
        max_bv_width: 32,
        mod_bound: 1000,
    };
    assert!(!cfg.enable_mod);
    assert_eq!(cfg.max_bv_width, 32);
    assert_eq!(cfg.mod_bound, 1000);
}

// =============================================================================
// Constraint management tests
// =============================================================================

#[test]
fn test_mathverse_ext_add_mod_constraints() {
    let mut solver = MathverseExtSolver::new(MathverseExtConfig::default());
    assert!(solver.mod_constraints().is_empty());

    solver.add_mod_constraint(ModConstraint {
        expr: LinearExpr::var(0),
        modulus: 3,
        remainder: 2,
    });
    solver.add_mod_constraint(ModConstraint {
        expr: LinearExpr::var(0),
        modulus: 5,
        remainder: 3,
    });

    assert_eq!(solver.mod_constraints().len(), 2);
    assert_eq!(solver.mod_constraints()[0].modulus, 3);
    assert_eq!(solver.mod_constraints()[1].remainder, 3);
}

#[test]
fn test_mathverse_ext_add_bv_constraints() {
    let mut solver = MathverseExtSolver::new(MathverseExtConfig::default());
    assert!(solver.bv_constraints().is_empty());

    solver.add_bv_constraint(BvConstraint {
        width: 8,
        op: BvOp::And,
        args: vec![BvTerm::Var("x".into()), BvTerm::Var("y".into())],
    });

    assert_eq!(solver.bv_constraints().len(), 1);
    assert_eq!(solver.bv_constraints()[0].width, 8);
}

// =============================================================================
// Chinese Remainder Theorem tests
// =============================================================================

#[test]
fn test_mathverse_ext_crt_two_congruences() {
    // x ≡ 2 (mod 3), x ≡ 3 (mod 5)  =>  x ≡ 8 (mod 15)
    let result = chinese_remainder(2, 3, 3, 5);
    assert!(result.is_some());
    let (r, m) = result.unwrap();
    assert_eq!(m, 15);
    assert_eq!(r, 8);
    // Verify: 8 % 3 == 2, 8 % 5 == 3
    assert_eq!(8 % 3, 2);
    assert_eq!(8 % 5, 3);
}

#[test]
fn test_mathverse_ext_crt_coprime_moduli() {
    // x ≡ 1 (mod 2), x ≡ 2 (mod 3)  =>  x ≡ 5 (mod 6)
    let result = chinese_remainder(1, 2, 2, 3);
    assert!(result.is_some());
    let (r, m) = result.unwrap();
    assert_eq!(m, 6);
    assert_eq!(r, 5);
    assert_eq!(5 % 2, 1);
    assert_eq!(5 % 3, 2);
}

#[test]
fn test_mathverse_ext_crt_no_solution_incompatible() {
    // x ≡ 0 (mod 2), x ≡ 1 (mod 2) - impossible
    let result = chinese_remainder(0, 2, 1, 2);
    assert!(result.is_none());
}

#[test]
fn test_mathverse_ext_crt_same_modulus_compatible() {
    // x ≡ 3 (mod 5), x ≡ 3 (mod 5) - trivially compatible
    let result = chinese_remainder(3, 5, 3, 5);
    assert!(result.is_some());
    let (r, m) = result.unwrap();
    assert_eq!(m, 5);
    assert_eq!(r, 3);
}

#[test]
fn test_mathverse_ext_crt_zero_modulus() {
    let result = chinese_remainder(1, 0, 2, 3);
    assert!(result.is_none());
}

// =============================================================================
// BV to linear conversion tests
// =============================================================================

#[test]
fn test_mathverse_ext_bv_to_linear_and() {
    let solver = MathverseExtSolver::new(MathverseExtConfig::default());
    let c = BvConstraint {
        width: 4,
        op: BvOp::And,
        args: vec![BvTerm::Var("x".into()), BvTerm::Var("y".into())],
    };
    let result = solver.bv_to_linear(&c);
    assert!(result.is_ok());
    let constraints = result.unwrap();
    // 4 bits * 2 constraints each (>= 0 and <= 1) = 8
    assert_eq!(constraints.len(), 8);
}

#[test]
fn test_mathverse_ext_bv_to_linear_or() {
    let solver = MathverseExtSolver::new(MathverseExtConfig::default());
    let c = BvConstraint {
        width: 2,
        op: BvOp::Or,
        args: vec![BvTerm::Var("a".into()), BvTerm::Var("b".into())],
    };
    let constraints = solver.bv_to_linear(&c).unwrap();
    assert_eq!(constraints.len(), 4); // 2 bits * 2 constraints each
}

#[test]
fn test_mathverse_ext_bv_to_linear_xor() {
    let solver = MathverseExtSolver::new(MathverseExtConfig::default());
    let c = BvConstraint {
        width: 1,
        op: BvOp::Xor,
        args: vec![BvTerm::Lit(1, 1), BvTerm::Lit(0, 1)],
    };
    let constraints = solver.bv_to_linear(&c).unwrap();
    assert_eq!(constraints.len(), 2); // 1 bit * 2 constraints
}

#[test]
fn test_mathverse_ext_bv_unsigned_comparison_ult() {
    let solver = MathverseExtSolver::new(MathverseExtConfig::default());
    let c = BvConstraint {
        width: 8,
        op: BvOp::Ult,
        args: vec![BvTerm::Var("a".into()), BvTerm::Var("b".into())],
    };
    let constraints = solver.bv_to_linear(&c).unwrap();
    // 1 comparison + 2 non-negative + 2 upper bound = 5
    assert_eq!(constraints.len(), 5);
}

#[test]
fn test_mathverse_ext_bv_unsigned_comparison_ule() {
    let solver = MathverseExtSolver::new(MathverseExtConfig::default());
    let c = BvConstraint {
        width: 16,
        op: BvOp::Ule,
        args: vec![BvTerm::Var("x".into()), BvTerm::Var("y".into())],
    };
    let constraints = solver.bv_to_linear(&c).unwrap();
    assert_eq!(constraints.len(), 5);
}

// =============================================================================
// Solver integration tests
// =============================================================================

#[test]
fn test_mathverse_ext_solve_simple_mod_system() {
    let mut solver = MathverseExtSolver::new(MathverseExtConfig::default());
    // x ≡ 2 (mod 3), x ≡ 3 (mod 5)  =>  x ≡ 8 (mod 15): SAT
    solver.add_mod_constraint(ModConstraint {
        expr: LinearExpr::var(0),
        modulus: 3,
        remainder: 2,
    });
    solver.add_mod_constraint(ModConstraint {
        expr: LinearExpr::var(0),
        modulus: 5,
        remainder: 3,
    });

    let result = solver.solve_mod().unwrap();
    assert!(result);
}

#[test]
fn test_mathverse_ext_solve_unsat_mod_system() {
    let mut solver = MathverseExtSolver::new(MathverseExtConfig::default());
    // x ≡ 0 (mod 4), x ≡ 2 (mod 4) - impossible
    solver.add_mod_constraint(ModConstraint {
        expr: LinearExpr::var(0),
        modulus: 4,
        remainder: 0,
    });
    solver.add_mod_constraint(ModConstraint {
        expr: LinearExpr::var(0),
        modulus: 4,
        remainder: 2,
    });

    let result = solver.solve_mod().unwrap();
    assert!(!result);
}

#[test]
fn test_mathverse_ext_bv_width_validation_exceeds_max() {
    let cfg = MathverseExtConfig {
        max_bv_width: 8,
        ..MathverseExtConfig::default()
    };
    let solver = MathverseExtSolver::new(cfg);
    let c = BvConstraint {
        width: 16,
        op: BvOp::Add,
        args: vec![BvTerm::Var("x".into()), BvTerm::Var("y".into())],
    };
    let result = solver.bv_to_linear(&c);
    assert!(result.is_err());
}

#[test]
fn test_mathverse_ext_extract_valid() {
    let solver = MathverseExtSolver::new(MathverseExtConfig::default());
    let c = BvConstraint {
        width: 32,
        op: BvOp::Extract { hi: 15, lo: 8 },
        args: vec![BvTerm::Var("x".into())],
    };
    let constraints = solver.bv_to_linear(&c).unwrap();
    assert_eq!(constraints.len(), 2); // >= 0 and < 2^8
}

#[test]
fn test_mathverse_ext_extract_invalid_range() {
    let solver = MathverseExtSolver::new(MathverseExtConfig::default());
    let c = BvConstraint {
        width: 8,
        op: BvOp::Extract { hi: 10, lo: 0 },
        args: vec![BvTerm::Var("x".into())],
    };
    let result = solver.bv_to_linear(&c);
    assert!(result.is_err());
}

#[test]
fn test_mathverse_ext_concat_operation() {
    let solver = MathverseExtSolver::new(MathverseExtConfig::default());
    let c = BvConstraint {
        width: 16,
        op: BvOp::Concat,
        args: vec![BvTerm::Var("hi".into()), BvTerm::Lit(0xFF, 8)],
    };
    let constraints = solver.bv_to_linear(&c).unwrap();
    // Should have an equality constraint for concat semantics
    assert!(!constraints.is_empty());
}

#[test]
fn test_mathverse_ext_combined_solve_sat() {
    let mut solver = MathverseExtSolver::new(MathverseExtConfig::default());

    // Mod constraint: x ≡ 1 (mod 3)
    solver.add_mod_constraint(ModConstraint {
        expr: LinearExpr::var(0),
        modulus: 3,
        remainder: 1,
    });

    // BV constraint: y AND z (width 4)
    solver.add_bv_constraint(BvConstraint {
        width: 4,
        op: BvOp::And,
        args: vec![BvTerm::Var("y".into()), BvTerm::Var("z".into())],
    });

    let result = solver.solve().unwrap();
    assert!(result);
}

#[test]
fn test_mathverse_ext_config_bv_disabled_rejects_bv() {
    let cfg = MathverseExtConfig {
        enable_bv: false,
        ..MathverseExtConfig::default()
    };
    let solver = MathverseExtSolver::new(cfg);
    let c = BvConstraint {
        width: 8,
        op: BvOp::Add,
        args: vec![BvTerm::Var("x".into())],
    };
    let result = solver.bv_to_linear(&c);
    assert!(result.is_err());
}

#[test]
fn test_mathverse_ext_config_mod_disabled_rejects_mod() {
    let cfg = MathverseExtConfig {
        enable_mod: false,
        ..MathverseExtConfig::default()
    };
    let solver = MathverseExtSolver::new(cfg);
    let result = solver.solve_mod();
    assert!(result.is_err());
}

#[test]
fn test_mathverse_ext_empty_constraints_sat() {
    let solver = MathverseExtSolver::new(MathverseExtConfig::default());
    let result = solver.solve().unwrap();
    assert!(result);
}

#[test]
fn test_mathverse_ext_bv_zero_width() {
    let solver = MathverseExtSolver::new(MathverseExtConfig::default());
    let c = BvConstraint {
        width: 0,
        op: BvOp::And,
        args: vec![],
    };
    let constraints = solver.bv_to_linear(&c).unwrap();
    assert!(constraints.is_empty());
}

#[test]
fn test_mathverse_ext_zero_extend() {
    let solver = MathverseExtSolver::new(MathverseExtConfig::default());
    let c = BvConstraint {
        width: 8,
        op: BvOp::ZeroExtend(8),
        args: vec![BvTerm::Var("x".into())],
    };
    let constraints = solver.bv_to_linear(&c).unwrap();
    // >= 0 and < 2^16
    assert_eq!(constraints.len(), 2);
}

#[test]
fn test_mathverse_ext_sign_extend() {
    let solver = MathverseExtSolver::new(MathverseExtConfig::default());
    let c = BvConstraint {
        width: 8,
        op: BvOp::SignExtend(8),
        args: vec![BvTerm::Var("x".into())],
    };
    let constraints = solver.bv_to_linear(&c).unwrap();
    // -2^15 <= val < 2^15
    assert_eq!(constraints.len(), 2);
}
