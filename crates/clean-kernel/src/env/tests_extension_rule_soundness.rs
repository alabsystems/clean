// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for concrete extension rule soundness declarations.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::ExprKind;
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_extension_rule_soundness()
        .expect("init_extension_rule_soundness");
    env
}

#[test]
fn test_extension_soundness_prop_form_registered() {
    let env = make_env();
    assert!(env
        .get_const(&Name::from_string("ExtensionSoundness.PropForm"))
        .is_some());
}

#[test]
fn test_extension_soundness_prop_form_constructors_registered() {
    let env = make_env();
    for name in [
        "ExtensionSoundness.PropForm.Var",
        "ExtensionSoundness.PropForm.Neg",
        "ExtensionSoundness.PropForm.Conj",
        "ExtensionSoundness.PropForm.Disj",
        "ExtensionSoundness.PropForm.Impl",
        "ExtensionSoundness.PropForm.Iff",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

#[test]
fn test_extension_soundness_all_definitions_registered() {
    let env = make_env();
    for name in [
        "ExtensionSoundness.PropForm",
        "ExtensionSoundness.PropForm.Var",
        "ExtensionSoundness.PropForm.Neg",
        "ExtensionSoundness.PropForm.Conj",
        "ExtensionSoundness.PropForm.Disj",
        "ExtensionSoundness.PropForm.Impl",
        "ExtensionSoundness.PropForm.Iff",
        "ExtensionSoundness.Assignment",
        "ExtensionSoundness.eval",
        "ExtensionSoundness.satisfiable",
        "ExtensionSoundness.vars_of",
        "ExtensionSoundness.fresh_for",
        "ExtensionSoundness.extend_def",
        "ExtensionSoundness.assign_extend",
        "ExtensionSoundness.assign_restrict",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

#[test]
fn test_extension_soundness_prop_form_type_checks() {
    let env = make_env();
    let prop_form =
        crate::expr::Expr::const_(Name::from_string("ExtensionSoundness.PropForm"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&prop_form)
        .expect("infer ExtensionSoundness.PropForm type");
    assert!(matches!(ty.kind(), ExprKind::Sort(..)));
}

#[test]
fn test_extension_soundness_assignment_type_checks() {
    let env = make_env();
    let assignment =
        crate::expr::Expr::const_(Name::from_string("ExtensionSoundness.Assignment"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&assignment)
        .expect("infer ExtensionSoundness.Assignment type");
    assert!(matches!(ty.kind(), ExprKind::Sort(..)));
}

#[test]
fn test_extension_soundness_eval_type_checks() {
    let env = make_env();
    let eval = crate::expr::Expr::const_(Name::from_string("ExtensionSoundness.eval"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&eval)
        .expect("infer ExtensionSoundness.eval type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_extension_soundness_extend_def_type_checks() {
    let env = make_env();
    let extend_def =
        crate::expr::Expr::const_(Name::from_string("ExtensionSoundness.extend_def"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&extend_def)
        .expect("infer ExtensionSoundness.extend_def type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_extension_soundness_idempotent() {
    let mut env = Environment::new();
    env.init_extension_rule_soundness().expect("first init");
    env.init_extension_rule_soundness().expect("second init");
}

#[test]
fn test_extension_soundness_naming_convention() {
    let env = make_env();
    for name in [
        "ExtensionSoundness.PropForm",
        "ExtensionSoundness.Assignment",
        "ExtensionSoundness.eval",
        "ExtensionSoundness.satisfiable",
        "ExtensionSoundness.vars_of",
        "ExtensionSoundness.fresh_for",
        "ExtensionSoundness.extend_def",
        "ExtensionSoundness.assign_extend",
        "ExtensionSoundness.assign_restrict",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered with ExtensionSoundness. prefix",
        );
    }
    for name in [
        "PropForm",
        "Assignment",
        "eval",
        "satisfiable",
        "vars_of",
        "fresh_for",
        "extend_def",
        "assign_extend",
        "assign_restrict",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_none(),
            "{name} should NOT be registered without ExtensionSoundness. prefix",
        );
    }
}

#[test]
fn test_extension_soundness_definition_vs_axiom_classification() {
    let env = make_env();
    for name in [
        "ExtensionSoundness.PropForm",
        "ExtensionSoundness.Assignment",
        "ExtensionSoundness.eval",
        "ExtensionSoundness.satisfiable",
        "ExtensionSoundness.vars_of",
        "ExtensionSoundness.fresh_for",
        "ExtensionSoundness.extend_def",
        "ExtensionSoundness.assign_extend",
        "ExtensionSoundness.assign_restrict",
    ] {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist"));
        assert_eq!(info.kind, ConstantKind::Axiom, "{name} should be an axiom");
    }
}

#[test]
fn test_extension_soundness_dependency_initialization() {
    let env = make_env();
    assert!(env.get_const(&Name::from_string("Bool")).is_some());
    assert!(env.get_const(&Name::from_string("Nat")).is_some());
    assert!(env
        .get_const(&Name::from_string("ProofTheory.VarSet"))
        .is_some());
}

// ====================================================================
// Theorem registration tests
// ====================================================================

#[test]
fn test_extension_soundness_all_theorems_registered() {
    let env = make_env();
    for name in [
        "ExtensionSoundness.extension_forward",
        "ExtensionSoundness.extension_reverse",
        "ExtensionSoundness.extension_equisatisfiable",
        "ExtensionSoundness.extension_preserves_model",
        "ExtensionSoundness.extension_projection",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

#[test]
fn test_extension_soundness_all_helpers_registered() {
    let env = make_env();
    for name in [
        "ExtensionSoundness.extension_forward_helper",
        "ExtensionSoundness.extension_reverse_helper",
        "ExtensionSoundness.extension_equisatisfiable_helper",
        "ExtensionSoundness.extension_preserves_model_helper",
        "ExtensionSoundness.extension_projection_helper",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} helper should be registered"
        );
    }
}

#[test]
fn test_extension_forward_type_checks() {
    let env = make_env();
    let thm = crate::expr::Expr::const_(
        Name::from_string("ExtensionSoundness.extension_forward"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("infer ExtensionSoundness.extension_forward type");
    // extension_forward : forall (f g : PropForm) (y : Nat), ...
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_extension_reverse_type_checks() {
    let env = make_env();
    let thm = crate::expr::Expr::const_(
        Name::from_string("ExtensionSoundness.extension_reverse"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("infer ExtensionSoundness.extension_reverse type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_extension_equisatisfiable_type_checks() {
    let env = make_env();
    let thm = crate::expr::Expr::const_(
        Name::from_string("ExtensionSoundness.extension_equisatisfiable"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("infer ExtensionSoundness.extension_equisatisfiable type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_extension_preserves_model_type_checks() {
    let env = make_env();
    let thm = crate::expr::Expr::const_(
        Name::from_string("ExtensionSoundness.extension_preserves_model"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("infer ExtensionSoundness.extension_preserves_model type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_extension_projection_type_checks() {
    let env = make_env();
    let thm = crate::expr::Expr::const_(
        Name::from_string("ExtensionSoundness.extension_projection"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&thm)
        .expect("infer ExtensionSoundness.extension_projection type");
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_extension_forward_helper_type_checks() {
    let env = make_env();
    let helper = crate::expr::Expr::const_(
        Name::from_string("ExtensionSoundness.extension_forward_helper"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&helper)
        .expect("infer ExtensionSoundness.extension_forward_helper type");
    // Helper is a Pi type: (f g : PropForm) -> (y : Nat) -> ...
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_extension_soundness_theorems_are_axioms() {
    let env = make_env();
    for name in [
        "ExtensionSoundness.extension_forward",
        "ExtensionSoundness.extension_forward_helper",
        "ExtensionSoundness.extension_reverse",
        "ExtensionSoundness.extension_reverse_helper",
        "ExtensionSoundness.extension_equisatisfiable",
        "ExtensionSoundness.extension_equisatisfiable_helper",
        "ExtensionSoundness.extension_preserves_model",
        "ExtensionSoundness.extension_preserves_model_helper",
        "ExtensionSoundness.extension_projection",
        "ExtensionSoundness.extension_projection_helper",
    ] {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist"));
        assert_eq!(info.kind, ConstantKind::Axiom, "{name} should be an axiom");
    }
}

#[test]
fn test_extension_soundness_fresh_for_type_checks() {
    let env = make_env();
    let fresh_for =
        crate::expr::Expr::const_(Name::from_string("ExtensionSoundness.fresh_for"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&fresh_for)
        .expect("infer ExtensionSoundness.fresh_for type");
    // fresh_for : Nat -> PropForm -> Prop
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_extension_soundness_satisfiable_type_checks() {
    let env = make_env();
    let satisfiable =
        crate::expr::Expr::const_(Name::from_string("ExtensionSoundness.satisfiable"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&satisfiable)
        .expect("infer ExtensionSoundness.satisfiable type");
    // satisfiable : PropForm -> Prop
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_extension_soundness_assign_extend_type_checks() {
    let env = make_env();
    let assign_ext = crate::expr::Expr::const_(
        Name::from_string("ExtensionSoundness.assign_extend"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&assign_ext)
        .expect("infer ExtensionSoundness.assign_extend type");
    // assign_extend : Assignment -> Nat -> Bool -> Assignment
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_extension_soundness_assign_restrict_type_checks() {
    let env = make_env();
    let assign_restrict = crate::expr::Expr::const_(
        Name::from_string("ExtensionSoundness.assign_restrict"),
        vec![],
    );
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&assign_restrict)
        .expect("infer ExtensionSoundness.assign_restrict type");
    // assign_restrict : Assignment -> Nat -> Assignment
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}

#[test]
fn test_extension_soundness_vars_of_type_checks() {
    let env = make_env();
    let vars_of =
        crate::expr::Expr::const_(Name::from_string("ExtensionSoundness.vars_of"), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let ty = tc
        .infer_type(&vars_of)
        .expect("infer ExtensionSoundness.vars_of type");
    // vars_of : PropForm -> VarSet
    assert!(matches!(ty.kind(), ExprKind::Pi(..)));
}
