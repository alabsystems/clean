// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extension rule soundness formalization.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::ExprKind;
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_extension_rule().expect("init_extension_rule");
    env
}

#[test]
fn test_extension_variable_registered() {
    let env = make_env();
    for name in [
        "ProofTheory.ExtensionVariable",
        "ProofTheory.ExtensionVariable.mk",
        "ProofTheory.ExtensionVariable.var_index",
        "ProofTheory.ExtensionVariable.defining_formula",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

#[test]
fn test_extended_resolution_proof_registered() {
    let env = make_env();
    for name in [
        "ProofTheory.ExtendedResolutionProof",
        "ProofTheory.ExtendedResolutionProof.Base",
        "ProofTheory.ExtendedResolutionProof.Extend",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

#[test]
fn test_all_definitions_registered() {
    let env = make_env();
    for name in [
        "ProofTheory.ExtensionVariable",
        "ProofTheory.ExtensionVariable.mk",
        "ProofTheory.ExtensionVariable.var_index",
        "ProofTheory.ExtensionVariable.defining_formula",
        "ProofTheory.ExtendedResolutionProof",
        "ProofTheory.ExtendedResolutionProof.Base",
        "ProofTheory.ExtendedResolutionProof.Extend",
        "ProofTheory.extension_complexity",
        "ProofTheory.tseitin_transform",
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
        "ProofTheory.extension_rule_sound",
        "ProofTheory.extended_resolution_complete",
        "ProofTheory.tseitin_equisatisfiable",
        "ProofTheory.extension_exponential_speedup",
        "ProofTheory.er_simulates_frege",
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
        "ProofTheory.extension_rule_sound_helper",
        "ProofTheory.extended_resolution_complete_helper",
        "ProofTheory.tseitin_equisatisfiable_helper",
        "ProofTheory.extension_exponential_speedup_helper",
        "ProofTheory.er_simulates_frege_helper",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} helper should be registered"
        );
    }
}

#[test]
fn test_extension_complexity_type_checks() {
    let env = make_env();
    let ext_complexity = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.extension_complexity"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&ext_complexity)
        .expect("infer ProofTheory.extension_complexity type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_tseitin_transform_type_checks() {
    let env = make_env();
    let tseitin =
        crate::expr::Expr::const_(Name::from_string("ProofTheory.tseitin_transform"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&tseitin)
        .expect("infer ProofTheory.tseitin_transform type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_extension_rule_sound_type_checks() {
    let env = make_env();
    let thm = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.extension_rule_sound"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("infer ProofTheory.extension_rule_sound type");
    // extension_rule_sound : forall (ev : ExtensionVariable) (f : CNF), ...
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_extended_resolution_complete_type_checks() {
    let env = make_env();
    let thm = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.extended_resolution_complete"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("infer ProofTheory.extended_resolution_complete type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_tseitin_equisatisfiable_type_checks() {
    let env = make_env();
    let thm = crate::expr::Expr::const_(
        Name::from_string("ProofTheory.tseitin_equisatisfiable"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("infer ProofTheory.tseitin_equisatisfiable type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_er_simulates_frege_type_checks() {
    let env = make_env();
    let thm =
        crate::expr::Expr::const_(Name::from_string("ProofTheory.er_simulates_frege"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("infer ProofTheory.er_simulates_frege type");
    // er_simulates_frege : forall (er frege : ProofSystem), ...
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_extension_rule().expect("first init");
    env.init_extension_rule().expect("second init");
}

#[test]
fn test_naming_convention() {
    let env = make_env();
    // All declarations should use ProofTheory. prefix
    for name in [
        "ProofTheory.ExtensionVariable",
        "ProofTheory.ExtendedResolutionProof",
        "ProofTheory.extension_complexity",
        "ProofTheory.tseitin_transform",
        "ProofTheory.extension_rule_sound",
        "ProofTheory.extended_resolution_complete",
        "ProofTheory.tseitin_equisatisfiable",
        "ProofTheory.extension_exponential_speedup",
        "ProofTheory.er_simulates_frege",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered with ProofTheory. prefix",
        );
    }
    // Bare names should not exist
    for name in [
        "ExtensionVariable",
        "ExtendedResolutionProof",
        "extension_complexity",
        "tseitin_transform",
        "extension_rule_sound",
        "er_simulates_frege",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_none(),
            "{name} should NOT be registered without ProofTheory. prefix",
        );
    }
}

#[test]
fn test_definition_vs_axiom_classification() {
    let env = make_env();
    // All extension rule declarations are axioms (opaque types/theorems)
    for name in [
        "ProofTheory.ExtensionVariable",
        "ProofTheory.ExtendedResolutionProof",
        "ProofTheory.extension_complexity",
        "ProofTheory.tseitin_transform",
        "ProofTheory.extension_rule_sound",
        "ProofTheory.extended_resolution_complete",
        "ProofTheory.tseitin_equisatisfiable",
        "ProofTheory.extension_exponential_speedup",
        "ProofTheory.er_simulates_frege",
    ] {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist"));
        assert_eq!(info.kind, ConstantKind::Axiom, "{name} should be an axiom");
    }
}

#[test]
fn test_dependency_initialization() {
    // init_extension_rule should also initialize its dependencies
    let env = make_env();
    // Check resolution complexity dependency
    assert!(env
        .get_const(&Name::from_string("ResComplexity.CNF"))
        .is_some());
    // Check proof hierarchy dependency
    assert!(env
        .get_const(&Name::from_string("ProofTheory.Formula"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("ProofTheory.ProofSystem"))
        .is_some());
}
