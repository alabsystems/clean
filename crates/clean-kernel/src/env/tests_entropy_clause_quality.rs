// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for entropy-based clause quality formalization.
//!
//! Part of #3167.

use crate::env::Environment;
use crate::expr::ExprKind;
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_entropy_clause_quality()
        .expect("init_entropy_clause_quality");
    env
}

#[test]
fn test_entropy_clause_quality_types_registered() {
    let env = make_env();
    for name in [
        "InfoTheory.EntropyClauseQuality.AssignmentSpace",
        "InfoTheory.EntropyClauseQuality.CNFFormula",
        "InfoTheory.EntropyClauseQuality.CNFClause",
        "InfoTheory.EntropyClauseQuality.SatisfyingSet",
        "InfoTheory.EntropyClauseQuality.RealNonneg",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered",
        );
    }
}

#[test]
fn test_entropy_clause_quality_operations_registered() {
    let env = make_env();
    for name in [
        "InfoTheory.EntropyClauseQuality.num_variables",
        "InfoTheory.EntropyClauseQuality.satisfying_set",
        "InfoTheory.EntropyClauseQuality.sat_count",
        "InfoTheory.EntropyClauseQuality.solution_entropy",
        "InfoTheory.EntropyClauseQuality.information_gain",
        "InfoTheory.EntropyClauseQuality.formula_union",
        "InfoTheory.EntropyClauseQuality.formula_add_clause",
        "InfoTheory.EntropyClauseQuality.formula_entails_clause",
        "InfoTheory.EntropyClauseQuality.assignment_satisfies_formula",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered",
        );
    }
}

#[test]
fn test_entropy_clause_quality_theorems_registered() {
    let env = make_env();
    for name in [
        "InfoTheory.EntropyClauseQuality.entropy_monotonicity",
        "InfoTheory.EntropyClauseQuality.submodularity",
        "InfoTheory.EntropyClauseQuality.entropy_nonneg",
        "InfoTheory.EntropyClauseQuality.entropy_upper_bound",
        "InfoTheory.EntropyClauseQuality.entropy_zero_iff_unique",
        "InfoTheory.EntropyClauseQuality.solution_count_monotone",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered",
        );
    }
}

#[test]
fn test_entropy_clause_quality_helpers_registered() {
    let env = make_env();
    for name in [
        "InfoTheory.EntropyClauseQuality.entropy_monotonicity_helper",
        "InfoTheory.EntropyClauseQuality.submodularity_helper",
        "InfoTheory.EntropyClauseQuality.entropy_nonneg_helper",
        "InfoTheory.EntropyClauseQuality.entropy_upper_bound_helper",
        "InfoTheory.EntropyClauseQuality.entropy_zero_iff_unique_helper",
        "InfoTheory.EntropyClauseQuality.solution_count_monotone_helper",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} helper should be registered",
        );
    }
}

#[test]
fn test_entropy_clause_quality_init_is_idempotent() {
    let mut env = Environment::new();
    env.init_entropy_clause_quality()
        .expect("first init_entropy_clause_quality");
    env.init_entropy_clause_quality()
        .expect("second init_entropy_clause_quality");
}

#[test]
fn test_assignment_space_type_checks() {
    let env = make_env();
    let c = crate::expr::Expr::const_(
        Name::from_string("InfoTheory.EntropyClauseQuality.AssignmentSpace"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&c).expect("infer AssignmentSpace type");
    assert!(matches!(ty.kind(), ExprKind::Sort(..)));
}

#[test]
fn test_real_nonneg_type_checks() {
    let env = make_env();
    let c = crate::expr::Expr::const_(
        Name::from_string("InfoTheory.EntropyClauseQuality.RealNonneg"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&c).expect("infer RealNonneg type");
    assert!(matches!(ty.kind(), ExprKind::Sort(..)));
}

#[test]
fn test_information_gain_type_checks() {
    let env = make_env();
    let c = crate::expr::Expr::const_(
        Name::from_string("InfoTheory.EntropyClauseQuality.information_gain"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&c).expect("infer information_gain type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_formula_entails_clause_type_checks() {
    let env = make_env();
    let c = crate::expr::Expr::const_(
        Name::from_string("InfoTheory.EntropyClauseQuality.formula_entails_clause"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&c)
        .expect("infer formula_entails_clause type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_assignment_satisfies_formula_type_checks() {
    let env = make_env();
    let c = crate::expr::Expr::const_(
        Name::from_string("InfoTheory.EntropyClauseQuality.assignment_satisfies_formula"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&c)
        .expect("infer assignment_satisfies_formula type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_entropy_monotonicity_type_checks() {
    let env = make_env();
    let c = crate::expr::Expr::const_(
        Name::from_string("InfoTheory.EntropyClauseQuality.entropy_monotonicity"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&c).expect("infer entropy_monotonicity type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}
