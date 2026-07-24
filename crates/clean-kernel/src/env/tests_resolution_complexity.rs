// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for resolution complexity and Haken's theorem formalization (S40).

use crate::env::Environment;
use crate::expr::ExprKind;
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_resolution_complexity()
        .expect("init_resolution_complexity");
    env
}

#[test]
fn test_literal_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("ResComplexity.Literal"))
        .is_some());
}

#[test]
fn test_cnf_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("ResComplexity.CNF"))
        .is_some());
}

#[test]
fn test_tree_res_proof_registered() {
    let env = make_env();
    for name in [
        "ResComplexity.TreeResProof",
        "ResComplexity.TreeResProof.Axiom",
        "ResComplexity.TreeResProof.Resolve",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

#[test]
fn test_php_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("ResComplexity.PHP"))
        .is_some());
}

#[test]
fn test_all_definitions_registered() {
    let env = make_env();
    for name in [
        "ResComplexity.Literal",
        "ResComplexity.Literal.mk",
        "ResComplexity.Literal.var",
        "ResComplexity.Literal.polarity",
        "ResComplexity.Clause",
        "ResComplexity.CNF",
        "ResComplexity.Assignment",
        "ResComplexity.SatisfiesClause",
        "ResComplexity.SatisfiesCNF",
        "ResComplexity.TreeResProof",
        "ResComplexity.tree_res_size",
        "ResComplexity.tree_res_refutes",
        "ResComplexity.PHP",
        "ResComplexity.QueryComplexity",
        "ResComplexity.ExponentialLowerBound",
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
        "ResComplexity.php_is_unsatisfiable",
        "ResComplexity.resolution_sound",
        "ResComplexity.tree_res_query_lb",
        "ResComplexity.php_adversary_strategy",
        "ResComplexity.php_query_complexity_exp",
        "ResComplexity.haken_theorem",
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
        "ResComplexity.php_unsat_helper",
        "ResComplexity.resolution_sound_helper",
        "ResComplexity.tree_res_query_lb_helper",
        "ResComplexity.php_query_exp_helper",
        "ResComplexity.haken_theorem_helper",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} helper should be registered"
        );
    }
}

#[test]
fn test_php_type_checks() {
    let env = make_env();
    let php = crate::expr::Expr::const_(Name::from_string("ResComplexity.PHP"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&php).expect("infer ResComplexity.PHP type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_haken_theorem_type_checks() {
    let env = make_env();
    let haken = crate::expr::Expr::const_(Name::from_string("ResComplexity.haken_theorem"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&haken)
        .expect("infer ResComplexity.haken_theorem type");
    // haken_theorem : forall (n : Nat) (p : TreeResProof), ...
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_resolution_complexity().expect("first init");
    env.init_resolution_complexity().expect("second init");
}

#[test]
fn test_naming_convention() {
    let env = make_env();
    // All declarations should use ResComplexity. prefix
    for name in [
        "ResComplexity.Literal",
        "ResComplexity.Clause",
        "ResComplexity.CNF",
        "ResComplexity.PHP",
        "ResComplexity.haken_theorem",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered with ResComplexity. prefix",
        );
    }
    // Bare names should not exist
    for name in ["Literal", "Clause", "CNF", "PHP", "haken_theorem"] {
        assert!(
            env.get_const(&Name::from_string(name)).is_none(),
            "{name} should NOT be registered without ResComplexity. prefix",
        );
    }
}
