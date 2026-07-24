// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for PB pigeonhole concrete PHP length-bound declarations.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::ExprKind;
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_pb_pigeonhole_length_bound()
        .expect("init_pb_pigeonhole_length_bound");
    env
}

#[test]
fn test_all_definitions_registered() {
    let env = make_env();
    for name in [
        "ProofTheory.CPProofOfPHP",
        "ProofTheory.cp_php_step_count",
        "ProofTheory.cp_php_axiom_count",
        "ProofTheory.cp_php_total_size",
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
        "ProofTheory.cp_php_size_cubic",
        "ProofTheory.cp_php_refutation_valid",
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
        "ProofTheory.cp_php_size_cubic_helper",
        "ProofTheory.cp_php_refutation_valid_helper",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} helper should be registered"
        );
    }
}

#[test]
fn test_cp_proof_of_php_type_checks() {
    let env = make_env();
    let expr = crate::expr::Expr::const_(Name::from_string("ProofTheory.CPProofOfPHP"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&expr)
        .expect("infer ProofTheory.CPProofOfPHP type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_cp_php_total_size_type_checks() {
    let env = make_env();
    let expr =
        crate::expr::Expr::const_(Name::from_string("ProofTheory.cp_php_total_size"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&expr)
        .expect("infer ProofTheory.cp_php_total_size type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_cp_php_size_cubic_type_checks() {
    let env = make_env();
    let expr =
        crate::expr::Expr::const_(Name::from_string("ProofTheory.cp_php_size_cubic"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&expr)
        .expect("infer ProofTheory.cp_php_size_cubic type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_cp_php_refutation_valid_type_checks() {
    let env = make_env();
    let expr = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.cp_php_refutation_valid"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&expr)
        .expect("infer ProofTheory.cp_php_refutation_valid type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_pb_pigeonhole_length_bound().expect("first init");
    env.init_pb_pigeonhole_length_bound().expect("second init");
}

#[test]
fn test_naming_convention() {
    let env = make_env();
    for name in [
        "ProofTheory.CPProofOfPHP",
        "ProofTheory.cp_php_step_count",
        "ProofTheory.cp_php_axiom_count",
        "ProofTheory.cp_php_total_size",
        "ProofTheory.cp_php_size_cubic",
        "ProofTheory.cp_php_refutation_valid",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered with ProofTheory. prefix"
        );
    }
    for name in [
        "CPProofOfPHP",
        "cp_php_step_count",
        "cp_php_axiom_count",
        "cp_php_total_size",
        "cp_php_size_cubic",
        "cp_php_refutation_valid",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_none(),
            "{name} should NOT be registered without ProofTheory. prefix"
        );
    }
}

#[test]
fn test_definition_vs_axiom_classification() {
    let env = make_env();
    for name in [
        "ProofTheory.CPProofOfPHP",
        "ProofTheory.cp_php_step_count",
        "ProofTheory.cp_php_axiom_count",
        "ProofTheory.cp_php_total_size",
        "ProofTheory.cp_php_size_cubic",
        "ProofTheory.cp_php_refutation_valid",
    ] {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist"));
        assert_eq!(info.kind, ConstantKind::Axiom, "{name} should be an axiom");
    }
}

#[test]
fn test_pb_pigeonhole_dependency() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("ProofTheory.PBProof"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("ProofTheory.pigeonhole_formula"))
        .is_some());
}

#[test]
fn test_le_dependency() {
    let env = make_env();
    assert!(env.get_const(&Name::from_string("LE.le")).is_some());
    assert!(env.get_const(&Name::from_string("instLENat")).is_some());
}
