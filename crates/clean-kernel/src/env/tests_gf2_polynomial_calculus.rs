// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for GF(2) Polynomial Calculus soundness formalization.
//!
//! Part of #3165.

use crate::env::Environment;
use crate::expr::ExprKind;
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_gf2_polynomial_calculus()
        .expect("init_gf2_polynomial_calculus");
    env
}

// ====================================================================
// Registration tests
// ====================================================================

#[test]
fn test_all_types_registered() {
    let env = make_env();
    for name in [
        "ProofTheory.GF2PolynomialCalculus.GF2Polynomial",
        "ProofTheory.GF2PolynomialCalculus.CNFClause",
        "ProofTheory.GF2PolynomialCalculus.CNFFormula",
        "ProofTheory.GF2PolynomialCalculus.BooleanAssignment",
        "ProofTheory.GF2PolynomialCalculus.gf2_one",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

#[test]
fn test_all_operations_registered() {
    let env = make_env();
    for name in [
        "ProofTheory.GF2PolynomialCalculus.clause_to_polynomial",
        "ProofTheory.GF2PolynomialCalculus.formula_ideal",
        "ProofTheory.GF2PolynomialCalculus.polynomial_evaluates_zero",
        "ProofTheory.GF2PolynomialCalculus.ideal_membership",
        "ProofTheory.GF2PolynomialCalculus.assignment_satisfies_clause",
        "ProofTheory.GF2PolynomialCalculus.assignment_satisfies_formula",
        "ProofTheory.GF2PolynomialCalculus.spoly_reduce",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

#[test]
fn test_all_theorems_registered() {
    let env = make_env();
    for name in [
        "ProofTheory.GF2PolynomialCalculus.clause_encoding_soundness",
        "ProofTheory.GF2PolynomialCalculus.gf2_field_idempotent",
        "ProofTheory.GF2PolynomialCalculus.ideal_closed_addition",
        "ProofTheory.GF2PolynomialCalculus.ideal_closed_multiplication",
        "ProofTheory.GF2PolynomialCalculus.pc_soundness_gf2",
        "ProofTheory.GF2PolynomialCalculus.spoly_preserves_ideal",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

#[test]
fn test_all_helper_axioms_registered() {
    let env = make_env();
    for name in [
        "ProofTheory.GF2PolynomialCalculus.clause_encoding_soundness_helper",
        "ProofTheory.GF2PolynomialCalculus.gf2_field_idempotent_helper",
        "ProofTheory.GF2PolynomialCalculus.ideal_closed_addition_helper",
        "ProofTheory.GF2PolynomialCalculus.ideal_closed_multiplication_helper",
        "ProofTheory.GF2PolynomialCalculus.pc_soundness_gf2_helper",
        "ProofTheory.GF2PolynomialCalculus.spoly_preserves_ideal_helper",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} helper should be registered"
        );
    }
}

// ====================================================================
// Type-checking tests
// ====================================================================

#[test]
fn test_gf2_polynomial_type_checks() {
    let env = make_env();
    let gf2p = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.GF2PolynomialCalculus.GF2Polynomial"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&gf2p).expect("infer GF2Polynomial type");
    // GF2Polynomial : Type 0, so its type is Sort(1)
    assert!(matches!(ty.kind(), ExprKind::Sort(..)));
}

#[test]
fn test_cnf_clause_type_checks() {
    let env = make_env();
    let cl = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.GF2PolynomialCalculus.CNFClause"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&cl).expect("infer CNFClause type");
    assert!(matches!(ty.kind(), ExprKind::Sort(..)));
}

#[test]
fn test_cnf_formula_type_checks() {
    let env = make_env();
    let f = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.GF2PolynomialCalculus.CNFFormula"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&f).expect("infer CNFFormula type");
    assert!(matches!(ty.kind(), ExprKind::Sort(..)));
}

#[test]
fn test_boolean_assignment_type_checks() {
    let env = make_env();
    let ba = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.GF2PolynomialCalculus.BooleanAssignment"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&ba).expect("infer BooleanAssignment type");
    assert!(matches!(ty.kind(), ExprKind::Sort(..)));
}

#[test]
fn test_gf2_one_type_checks() {
    let env = make_env();
    let one = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.GF2PolynomialCalculus.gf2_one"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&one).expect("infer gf2_one type");
    // gf2_one : GF2Polynomial, so type is a Const
    assert!(matches!(ty.kind(), ExprKind::Const(..)));
}

#[test]
fn test_clause_to_polynomial_type_checks() {
    let env = make_env();
    let ctp = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.GF2PolynomialCalculus.clause_to_polynomial"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&ctp)
        .expect("infer clause_to_polynomial type");
    // CNFClause -> GF2Polynomial
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_ideal_membership_type_checks() {
    let env = make_env();
    let im = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.GF2PolynomialCalculus.ideal_membership"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&im).expect("infer ideal_membership type");
    // GF2Polynomial -> CNFFormula -> Nat -> Prop (Pi type)
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_pc_soundness_gf2_type_checks() {
    let env = make_env();
    let thm = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.GF2PolynomialCalculus.pc_soundness_gf2"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&thm).expect("infer pc_soundness_gf2 type");
    // forall (f : CNFFormula) (n : Nat), ... (Pi type)
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_spoly_reduce_type_checks() {
    let env = make_env();
    let sr = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.GF2PolynomialCalculus.spoly_reduce"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&sr).expect("infer spoly_reduce type");
    // GF2Polynomial -> GF2Polynomial -> GF2Polynomial (Pi type)
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

// ====================================================================
// Idempotency test
// ====================================================================

#[test]
fn test_init_idempotent() {
    let mut env = Environment::new();
    env.init_gf2_polynomial_calculus().expect("first init");
    env.init_gf2_polynomial_calculus()
        .expect("second init should be idempotent");
}

// ====================================================================
// Total declaration count
// ====================================================================

#[test]
fn test_total_declarations_count() {
    let env = make_env();
    // 5 types + 7 operations + 6 helper axioms + 6 theorems = 24
    let all_names = [
        // Types
        "ProofTheory.GF2PolynomialCalculus.GF2Polynomial",
        "ProofTheory.GF2PolynomialCalculus.CNFClause",
        "ProofTheory.GF2PolynomialCalculus.CNFFormula",
        "ProofTheory.GF2PolynomialCalculus.BooleanAssignment",
        "ProofTheory.GF2PolynomialCalculus.gf2_one",
        // Operations
        "ProofTheory.GF2PolynomialCalculus.clause_to_polynomial",
        "ProofTheory.GF2PolynomialCalculus.formula_ideal",
        "ProofTheory.GF2PolynomialCalculus.polynomial_evaluates_zero",
        "ProofTheory.GF2PolynomialCalculus.ideal_membership",
        "ProofTheory.GF2PolynomialCalculus.assignment_satisfies_clause",
        "ProofTheory.GF2PolynomialCalculus.assignment_satisfies_formula",
        "ProofTheory.GF2PolynomialCalculus.spoly_reduce",
        // Helper axioms
        "ProofTheory.GF2PolynomialCalculus.clause_encoding_soundness_helper",
        "ProofTheory.GF2PolynomialCalculus.gf2_field_idempotent_helper",
        "ProofTheory.GF2PolynomialCalculus.ideal_closed_addition_helper",
        "ProofTheory.GF2PolynomialCalculus.ideal_closed_multiplication_helper",
        "ProofTheory.GF2PolynomialCalculus.pc_soundness_gf2_helper",
        "ProofTheory.GF2PolynomialCalculus.spoly_preserves_ideal_helper",
        // Theorems
        "ProofTheory.GF2PolynomialCalculus.clause_encoding_soundness",
        "ProofTheory.GF2PolynomialCalculus.gf2_field_idempotent",
        "ProofTheory.GF2PolynomialCalculus.ideal_closed_addition",
        "ProofTheory.GF2PolynomialCalculus.ideal_closed_multiplication",
        "ProofTheory.GF2PolynomialCalculus.pc_soundness_gf2",
        "ProofTheory.GF2PolynomialCalculus.spoly_preserves_ideal",
    ];
    for name in &all_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} not found"
        );
    }
    assert_eq!(all_names.len(), 24);
}
