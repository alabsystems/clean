// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Focused instance-elaboration regressions for #796.

use super::*;

#[test]
fn test_issue796_instance_field_uses_expected_type_for_anonymous_ctor() {
    let mut env = Environment::with_prelude();

    let box_decl = parse_decl_for_elab(
        r"structure Box where
          val : Nat",
    )
    .unwrap();
    crate::elaborate_decl_and_register(&mut env, &box_decl).expect("Box structure should register");

    let has_default_decl = parse_decl_for_elab(
        r"class HasDefault (α : Type) where
          default : α",
    )
    .unwrap();
    crate::elaborate_decl_and_register(&mut env, &has_default_decl)
        .expect("HasDefault class should register");

    let inst_decl = parse_decl_for_elab(
        r"instance : HasDefault Box where
          default := ⟨42⟩",
    )
    .unwrap();

    let result = crate::elaborate_decl_and_register(&mut env, &inst_decl);
    assert!(
        result.is_ok(),
        "instance field anonymous ctor should elaborate with field expected type: {result:?}"
    );
}

#[test]
fn test_issue796_instance_field_uses_expected_type_for_struct_literal() {
    let mut env = Environment::with_prelude();

    let box_decl = parse_decl_for_elab(
        r"structure Box where
          val : Nat",
    )
    .unwrap();
    crate::elaborate_decl_and_register(&mut env, &box_decl).expect("Box structure should register");

    let has_default_decl = parse_decl_for_elab(
        r"class HasDefault (α : Type) where
          default : α",
    )
    .unwrap();
    crate::elaborate_decl_and_register(&mut env, &has_default_decl)
        .expect("HasDefault class should register");

    let inst_decl = parse_decl_for_elab(
        r"instance : HasDefault Box where
          default := { val := 42 }",
    )
    .unwrap();

    let result = crate::elaborate_decl_and_register(&mut env, &inst_decl);
    assert!(
        result.is_ok(),
        "instance field struct literal should elaborate with field expected type: {result:?}"
    );
}

#[test]
fn test_issue796_instance_field_rejects_mismatched_expected_type() {
    let mut env = Environment::with_prelude();

    let box_decl = parse_decl_for_elab(
        r"structure Box where
          val : Nat",
    )
    .unwrap();
    crate::elaborate_decl_and_register(&mut env, &box_decl).expect("Box structure should register");

    let has_default_decl = parse_decl_for_elab(
        r"class HasDefault (α : Type) where
          default : α",
    )
    .unwrap();
    crate::elaborate_decl_and_register(&mut env, &has_default_decl)
        .expect("HasDefault class should register");

    let inst_decl = parse_decl_for_elab(
        r"instance : HasDefault Box where
          default := true",
    )
    .unwrap();

    let err = crate::elaborate_decl_and_register(&mut env, &inst_decl)
        .expect_err("mismatched instance field should be rejected");
    assert!(
        matches!(err, ElabError::TypeMismatch { .. }),
        "expected TypeMismatch for mismatched instance field, got {err:?}"
    );
}

#[test]
fn test_issue173_anonymous_constructor_rejects_mismatched_arg_type() {
    let mut env = Environment::with_prelude();

    let wrap_decl = parse_decl_for_elab(
        r"structure Wrap (A : Type) where
          val : A",
    )
    .unwrap();
    crate::elaborate_decl_and_register(&mut env, &wrap_decl)
        .expect("Wrap structure should register");

    let bad_decl = parse_decl_for_elab("def badWrap : Wrap Nat := ⟨true⟩").unwrap();
    let err = crate::elaborate_decl_and_register(&mut env, &bad_decl)
        .expect_err("mismatched anonymous-constructor argument should be rejected");
    assert!(
        matches!(err, ElabError::TypeMismatch { .. }),
        "expected TypeMismatch for mismatched anonymous constructor argument, got {err:?}"
    );
}

#[test]
fn test_issue1983_instance_type_instantiates_class_head_hole() {
    let mut env = Environment::with_prelude();

    let has_default_decl = parse_decl_for_elab(
        r"class HasDefault (α : Type) where
          default : α",
    )
    .unwrap();
    crate::elaborate_decl_and_register(&mut env, &has_default_decl)
        .expect("HasDefault class should register");

    let inst_decl = parse_decl_for_elab(
        r"instance instHasDefaultNat : HasDefault _ where
          default := 42",
    )
    .unwrap();
    crate::elaborate_decl_and_register(&mut env, &inst_decl)
        .expect("instance with class-head hole should register");

    let inst_info = env
        .get_const(&Name::from_string("instHasDefaultNat"))
        .expect("instHasDefaultNat should be registered");
    let expected_ty = Expr::app(
        Expr::const_(Name::from_string("HasDefault"), vec![]),
        Expr::const_(Name::from_string("Nat"), vec![]),
    );
    assert_eq!(
        inst_info.type_, expected_ty,
        "instance type should instantiate the class-head hole before registration"
    );
}

#[test]
#[serial_test::serial]
fn explicit_type_dec_eq_uses_the_registered_decidable_eq_evidence() {
    use clean_kernel::sorry::{reset_sorry_counter, synthetic_sorry_count};

    reset_sorry_counter();
    let baseline = synthetic_sorry_count();
    let env = Environment::with_prelude();
    let expr = elab_with_env(&env, "Nat.decEq 1 1")
        .expect("Nat.decEq should resolve through the registered DecidableEq evidence");

    let constants = expr.collect_constants();
    assert!(
        constants.iter().any(|name| {
            name == &Name::from_string("Nat.decEq")
                || name == &Name::from_string("instDecidableEqNat")
        }),
        "explicit Nat.decEq must retain genuine DecidableEq evidence: {expr:?}"
    );
    assert!(
        !expr.has_sorry(),
        "explicit Nat.decEq must be sorry-free: {expr:?}"
    );
    assert_eq!(
        synthetic_sorry_count(),
        baseline,
        "resolving an explicit decEq must not mint synthetic evidence"
    );
}

#[test]
#[serial_test::serial]
fn explicit_type_dec_eq_without_evidence_fails_without_sorry() {
    use clean_kernel::sorry::{reset_sorry_counter, synthetic_sorry_count};

    reset_sorry_counter();
    let baseline = synthetic_sorry_count();
    let mut env = Environment::with_prelude();
    let decl = parse_decl_for_elab("axiom UndecidableCarrier : Type").expect("parse carrier");
    crate::elaborate_decl_and_register(&mut env, &decl).expect("register carrier");
    let lhs = parse_decl_for_elab("axiom undecidableLeft : UndecidableCarrier").expect("parse lhs");
    crate::elaborate_decl_and_register(&mut env, &lhs).expect("register lhs");
    let rhs =
        parse_decl_for_elab("axiom undecidableRight : UndecidableCarrier").expect("parse rhs");
    crate::elaborate_decl_and_register(&mut env, &rhs).expect("register rhs");

    let error = elab_with_env(
        &env,
        "UndecidableCarrier.decEq undecidableLeft undecidableRight",
    )
    .expect_err("a carrier without DecidableEq evidence must fail closed");
    assert!(
        matches!(
            error,
            ElabError::FailedToSynthesizeInstance { ref goal }
                if goal.contains("Decidable") && goal.contains("UndecidableCarrier")
        ),
        "expected typed Decidable instance-synthesis failure, got {error:?}"
    );
    assert_eq!(
        synthetic_sorry_count(),
        baseline,
        "failed explicit decEq synthesis must not mint synthetic evidence"
    );
}
