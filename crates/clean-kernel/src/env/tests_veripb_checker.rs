// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for VeriPB proof certificate verification formalization.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::ExprKind;
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_veripb_checker().expect("init_veripb_checker");
    env
}

// ====================================================================
// Type registration tests
// ====================================================================

#[test]
fn test_pb_var_registered() {
    let env = make_env();
    assert!(env.get_const(&Name::from_string("VeriPB.PbVar")).is_some());
}

#[test]
fn test_pb_constraint_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("VeriPB.PbConstraint"))
        .is_some());
}

#[test]
fn test_assignment_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("VeriPB.Assignment"))
        .is_some());
}

#[test]
fn test_constraint_db_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("VeriPB.ConstraintDb"))
        .is_some());
}

#[test]
fn test_veripb_step_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("VeriPB.VeriPbStep"))
        .is_some());
}

// ====================================================================
// CP operation registration tests
// ====================================================================

#[test]
fn test_all_cp_operations_registered() {
    let env = make_env();
    for name in [
        "VeriPB.cp_add",
        "VeriPB.cp_multiply",
        "VeriPB.cp_divide",
        "VeriPB.cp_saturate",
        "VeriPB.cp_weaken",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

// ====================================================================
// Step constructor registration tests
// ====================================================================

#[test]
fn test_all_step_constructors_registered() {
    let env = make_env();
    for name in [
        "VeriPB.VeriPbStep.PolAdd",
        "VeriPB.VeriPbStep.PolMul",
        "VeriPB.VeriPbStep.PolDiv",
        "VeriPB.VeriPbStep.PolSat",
        "VeriPB.VeriPbStep.Weaken",
        "VeriPB.VeriPbStep.Rup",
        "VeriPB.VeriPbStep.Del",
        "VeriPB.VeriPbStep.Conclude",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

// ====================================================================
// Verifier registration tests
// ====================================================================

#[test]
fn test_verifier_functions_registered() {
    let env = make_env();
    for name in [
        "VeriPB.execute_step",
        "VeriPB.verify_certificate",
        "VeriPB.rup_check",
        "VeriPB.satisfies_constraint",
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
fn test_all_soundness_theorems_registered() {
    let env = make_env();
    for name in [
        "VeriPB.cp_add_sound",
        "VeriPB.cp_multiply_sound",
        "VeriPB.cp_divide_sound",
        "VeriPB.cp_saturate_sound",
        "VeriPB.cp_weaken_sound",
        "VeriPB.rup_sound",
        "VeriPB.step_sound",
        "VeriPB.verify_sound",
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
        "VeriPB.cp_add_sound_helper",
        "VeriPB.cp_multiply_sound_helper",
        "VeriPB.cp_divide_sound_helper",
        "VeriPB.cp_saturate_sound_helper",
        "VeriPB.cp_weaken_sound_helper",
        "VeriPB.rup_sound_helper",
        "VeriPB.step_sound_helper",
        "VeriPB.verify_sound_helper",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} helper should be registered"
        );
    }
}

// ====================================================================
// Type checking tests
// ====================================================================

#[test]
fn test_cp_add_type_checks() {
    let env = make_env();
    let cp_add = crate::expr::Expr::const_(Name::from_string("VeriPB.cp_add"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&cp_add).expect("infer VeriPB.cp_add type");
    // cp_add : PbConstraint -> PbConstraint -> PbConstraint
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_satisfies_constraint_type_checks() {
    let env = make_env();
    let sat = crate::expr::Expr::const_(Name::from_string("VeriPB.satisfies_constraint"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&sat)
        .expect("infer VeriPB.satisfies_constraint type");
    // satisfies_constraint : Assignment -> PbConstraint -> Prop
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_verify_certificate_type_checks() {
    let env = make_env();
    let vc = crate::expr::Expr::const_(Name::from_string("VeriPB.verify_certificate"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&vc)
        .expect("infer VeriPB.verify_certificate type");
    // verify_certificate : ConstraintDb -> List VeriPbStep -> Bool
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_verify_sound_type_checks() {
    let env = make_env();
    let vs = crate::expr::Expr::const_(Name::from_string("VeriPB.verify_sound"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&vs).expect("infer VeriPB.verify_sound type");
    // verify_sound : forall (db : ConstraintDb), verify_sound_helper db
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_cp_add_sound_type_checks() {
    let env = make_env();
    let thm = crate::expr::Expr::const_(Name::from_string("VeriPB.cp_add_sound"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&thm).expect("infer VeriPB.cp_add_sound type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_step_sound_type_checks() {
    let env = make_env();
    let thm = crate::expr::Expr::const_(Name::from_string("VeriPB.step_sound"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc.infer_type(&thm).expect("infer VeriPB.step_sound type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

// ====================================================================
// Idempotency test
// ====================================================================

#[test]
fn test_idempotent() {
    let mut env = Environment::new();
    env.init_veripb_checker().expect("first init");
    env.init_veripb_checker().expect("second init");
}

// ====================================================================
// Naming convention test
// ====================================================================

#[test]
fn test_naming_convention() {
    let env = make_env();
    // All declarations should use VeriPB. prefix
    for name in [
        "VeriPB.PbVar",
        "VeriPB.PbConstraint",
        "VeriPB.Assignment",
        "VeriPB.ConstraintDb",
        "VeriPB.VeriPbStep",
        "VeriPB.cp_add",
        "VeriPB.cp_multiply",
        "VeriPB.cp_divide",
        "VeriPB.cp_saturate",
        "VeriPB.cp_weaken",
        "VeriPB.execute_step",
        "VeriPB.verify_certificate",
        "VeriPB.rup_check",
        "VeriPB.verify_sound",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered with VeriPB. prefix",
        );
    }
    // Bare names should not exist
    for name in [
        "PbVar",
        "PbConstraint",
        "Assignment",
        "ConstraintDb",
        "VeriPbStep",
        "cp_add",
        "verify_sound",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_none(),
            "{name} should NOT be registered without VeriPB. prefix",
        );
    }
}

// ====================================================================
// Classification test
// ====================================================================

#[test]
fn test_definition_vs_axiom_classification() {
    let env = make_env();
    // Definitions (have values)
    for name in ["VeriPB.Assignment", "VeriPB.ConstraintDb"] {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist"));
        assert_eq!(
            info.kind,
            ConstantKind::Definition,
            "{name} should be a definition"
        );
    }
    // Axioms (opaque types/operations)
    for name in [
        "VeriPB.PbVar",
        "VeriPB.PbConstraint",
        "VeriPB.VeriPbStep",
        "VeriPB.cp_add",
        "VeriPB.verify_sound",
    ] {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist"));
        assert_eq!(info.kind, ConstantKind::Axiom, "{name} should be an axiom");
    }
}

// ====================================================================
// Dependency test
// ====================================================================

#[test]
fn test_cutting_planes_dependency() {
    // init_veripb_checker should also initialize cutting planes
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("ProofTheory.CuttingPlanesProof"))
        .is_some());
    assert!(env
        .get_const(&Name::from_string("ProofTheory.LinearInequality"))
        .is_some());
}

// ====================================================================
// Declaration count test
// ====================================================================

#[test]
fn test_total_declaration_count() {
    let env = make_env();
    // 5 types + 5 CP ops + 1 satisfies + 1 step type + 8 step constructors
    // + 3 verifier fns + 8 helper axioms + 8 theorems = 39 VeriPB declarations
    let veripb_count = env
        .constants()
        .filter(|c| c.name.to_string().starts_with("VeriPB."))
        .count();
    assert!(
        veripb_count >= 37,
        "Expected at least 37 VeriPB declarations, got {veripb_count}"
    );
}
