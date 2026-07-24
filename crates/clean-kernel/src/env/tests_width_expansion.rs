// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for width-expansion theorem formalization (Ben-Sasson-Wigderson).

use crate::env::Environment;
use crate::expr::ExprKind;
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_width_expansion().expect("init_width_expansion");
    env
}

// ====================================================================
// Definition registration tests
// ====================================================================

#[test]
fn test_incidence_graph_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("WidthExpansion.IncidenceGraph"))
        .is_some());
}

#[test]
fn test_variable_set_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("WidthExpansion.VariableSet"))
        .is_some());
}

#[test]
fn test_resolution_proof_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("WidthExpansion.ResolutionProof"))
        .is_some());
}

#[test]
fn test_all_definitions_registered() {
    let env = make_env();
    for name in [
        "WidthExpansion.IncidenceGraph",
        "WidthExpansion.VariableSet",
        "WidthExpansion.ClauseSet",
        "WidthExpansion.incidence_graph",
        "WidthExpansion.variables",
        "WidthExpansion.clauses",
        "WidthExpansion.num_variables",
        "WidthExpansion.num_clauses",
        "WidthExpansion.neighborhood",
        "WidthExpansion.clause_neighborhood",
        "WidthExpansion.set_size_var",
        "WidthExpansion.set_size_clause",
        "WidthExpansion.boundary_expansion",
        "WidthExpansion.ResolutionProof",
        "WidthExpansion.is_refutation",
        "WidthExpansion.proof_width",
        "WidthExpansion.PartialAssignment",
        "WidthExpansion.restrict",
        "WidthExpansion.restriction_size",
        "WidthExpansion.initial_width",
        "WidthExpansion.spectral_gap",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

// ====================================================================
// Theorem registration tests
// ====================================================================

#[test]
fn test_all_theorems_registered() {
    let env = make_env();
    for name in [
        "WidthExpansion.width_expansion",
        "WidthExpansion.expansion_monotone_restriction",
        "WidthExpansion.width_random_restriction",
        "WidthExpansion.size_width_relationship",
        "WidthExpansion.cheeger_inequality",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

#[test]
fn test_helper_axioms_registered() {
    let env = make_env();
    for name in [
        "WidthExpansion.width_expansion_helper",
        "WidthExpansion.expansion_monotone_restriction_helper",
        "WidthExpansion.width_random_restriction_helper",
        "WidthExpansion.size_width_helper",
        "WidthExpansion.cheeger_helper",
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
fn test_incidence_graph_type_checks() {
    let env = make_env();
    let ig = crate::expr::Expr::const_(Name::from_string("WidthExpansion.IncidenceGraph"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&ig)
        .expect("infer WidthExpansion.IncidenceGraph type");
    assert!(matches!(ty.kind(), ExprKind::Sort(..)));
}

#[test]
fn test_boundary_expansion_type_checks() {
    let env = make_env();
    let be = crate::expr::Expr::const_(
        Name::from_string("WidthExpansion.boundary_expansion"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&be)
        .expect("infer WidthExpansion.boundary_expansion type");
    // boundary_expansion : IncidenceGraph -> Nat
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_is_refutation_type_checks() {
    let env = make_env();
    let ir = crate::expr::Expr::const_(Name::from_string("WidthExpansion.is_refutation"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&ir)
        .expect("infer WidthExpansion.is_refutation type");
    // is_refutation : ResolutionProof -> CNF -> Prop
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_width_expansion_type_checks() {
    let env = make_env();
    let we = crate::expr::Expr::const_(Name::from_string("WidthExpansion.width_expansion"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&we)
        .expect("infer WidthExpansion.width_expansion type");
    // forall (f : CNF) (p : ResolutionProof), ...
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_expansion_monotone_restriction_type_checks() {
    let env = make_env();
    let emr = crate::expr::Expr::const_(
        Name::from_string("WidthExpansion.expansion_monotone_restriction"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&emr)
        .expect("infer WidthExpansion.expansion_monotone_restriction type");
    // forall (f : CNF) (rho : PartialAssignment), ...
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_size_width_relationship_type_checks() {
    let env = make_env();
    let swr = crate::expr::Expr::const_(
        Name::from_string("WidthExpansion.size_width_relationship"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&swr)
        .expect("infer WidthExpansion.size_width_relationship type");
    // forall (f : CNF), ...
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_cheeger_inequality_type_checks() {
    let env = make_env();
    let ci = crate::expr::Expr::const_(
        Name::from_string("WidthExpansion.cheeger_inequality"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&ci)
        .expect("infer WidthExpansion.cheeger_inequality type");
    // forall (f : CNF), ...
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

// ====================================================================
// Idempotency test
// ====================================================================

#[test]
fn test_init_idempotent() {
    let mut env = Environment::new();
    env.init_width_expansion()
        .expect("first init_width_expansion");
    env.init_width_expansion()
        .expect("second init_width_expansion should be idempotent");
}

// ====================================================================
// Total count test
// ====================================================================

#[test]
fn test_declaration_count() {
    let env = make_env();
    let all_names = [
        // 21 definitions
        "WidthExpansion.IncidenceGraph",
        "WidthExpansion.VariableSet",
        "WidthExpansion.ClauseSet",
        "WidthExpansion.incidence_graph",
        "WidthExpansion.variables",
        "WidthExpansion.clauses",
        "WidthExpansion.num_variables",
        "WidthExpansion.num_clauses",
        "WidthExpansion.neighborhood",
        "WidthExpansion.clause_neighborhood",
        "WidthExpansion.set_size_var",
        "WidthExpansion.set_size_clause",
        "WidthExpansion.boundary_expansion",
        "WidthExpansion.ResolutionProof",
        "WidthExpansion.is_refutation",
        "WidthExpansion.proof_width",
        "WidthExpansion.PartialAssignment",
        "WidthExpansion.restrict",
        "WidthExpansion.restriction_size",
        "WidthExpansion.initial_width",
        "WidthExpansion.spectral_gap",
        // 5 helpers + 5 theorems = 10
        "WidthExpansion.width_expansion_helper",
        "WidthExpansion.width_expansion",
        "WidthExpansion.expansion_monotone_restriction_helper",
        "WidthExpansion.expansion_monotone_restriction",
        "WidthExpansion.width_random_restriction_helper",
        "WidthExpansion.width_random_restriction",
        "WidthExpansion.size_width_helper",
        "WidthExpansion.size_width_relationship",
        "WidthExpansion.cheeger_helper",
        "WidthExpansion.cheeger_inequality",
    ];
    for name in &all_names {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} not found"
        );
    }
    // 21 definitions + 10 theorem/helper = 31 total WidthExpansion declarations
    assert_eq!(all_names.len(), 31);
}
