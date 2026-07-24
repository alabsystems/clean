// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::super::ay_solver::create_smt_backend;
use super::super::ay_types::{supported_local_decl_kind, SupportedLocalDeclKind};
use super::super::*;
use super::real_support::{int_le, real_lt, real_of_nat};
use crate::tactic::smt_translate::SmtSort;
use crate::tactic::LocalDecl;
use crate::unify::MetaState;
use clean_auto::bridge::ay_contract::{AyError, AyLogic};
use clean_kernel::{Expr, FVarId, Name};
use serial_test::serial;

fn supported_local_decl_smt_sort_for_test(lean_type: &Expr) -> Option<SmtSort> {
    match supported_local_decl_kind(lean_type)? {
        SupportedLocalDeclKind::Scalar(sort) => Some(sort),
        SupportedLocalDeclKind::Callable { .. } => None,
    }
}

#[test]
fn test_uint_types_rejected_from_smt_sort() {
    for type_name in &["UInt8", "UInt16", "UInt32", "UInt64", "Float"] {
        let ty = Expr::const_(Name::from_string(type_name), vec![]);
        assert_eq!(
            supported_local_decl_smt_sort_for_test(&ty),
            None,
            "{type_name} must not map to any SMT sort — domain semantics are unsound"
        );
    }
}

#[test]
fn test_nat_int_real_still_accepted() {
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let real_ty = Expr::const_(Name::from_string("Real"), vec![]);

    assert_eq!(
        supported_local_decl_smt_sort_for_test(&nat_ty),
        Some(SmtSort::Int),
        "Nat should still map to SmtSort::Int"
    );
    assert_eq!(
        supported_local_decl_smt_sort_for_test(&int_ty),
        Some(SmtSort::Int),
        "Int should still map to SmtSort::Int"
    );
    assert_eq!(
        supported_local_decl_smt_sort_for_test(&real_ty),
        Some(SmtSort::Real),
        "Real should still map to SmtSort::Real"
    );
}

// -- Callable result sort classification (#3073) --

#[test]
fn test_callable_int_to_real_classified_as_callable_real() {
    use clean_kernel::BinderInfo;
    // f : Int → Real
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let real_ty = Expr::const_(Name::from_string("Real"), vec![]);
    let pi_ty = Expr::pi(BinderInfo::Default, int_ty, real_ty);
    assert_eq!(
        supported_local_decl_kind(&pi_ty),
        Some(SupportedLocalDeclKind::Callable {
            result_sort: SmtSort::Real
        }),
        "Int → Real should classify as Callable with Real result sort"
    );
}

#[test]
fn test_callable_real_to_real_to_real_classified_correctly() {
    use clean_kernel::BinderInfo;
    // g : Real → Real → Real
    let real_ty = Expr::const_(Name::from_string("Real"), vec![]);
    let inner_pi = Expr::pi(BinderInfo::Default, real_ty.clone(), real_ty.clone());
    let outer_pi = Expr::pi(BinderInfo::Default, real_ty, inner_pi);
    assert_eq!(
        supported_local_decl_kind(&outer_pi),
        Some(SupportedLocalDeclKind::Callable {
            result_sort: SmtSort::Real
        }),
        "Real → Real → Real should classify as Callable with Real result sort"
    );
}

// -- Domain-mismatch rejection regressions (#2849) --

/// Fast-lane (TrustSolver) registration must reject UInt8 locals (#2849 AC3).
#[test]
#[serial]
fn test_trust_solver_rejects_uint8_local() {
    let config = AyConfig::default().with_verify_policy(SmtVerifyPolicy::TrustSolver);
    let fvar = FVarId::new(300);
    let uint8_ty = Expr::const_(Name::from_string("UInt8"), vec![]);
    let local_ctx = vec![LocalDecl {
        fvar,
        name: "x".to_string(),
        ty: uint8_ty,
        value: None,
    }];
    let mut solver = create_smt_backend(&config, AyLogic::QfLia);
    let result = solver.register_fvars_from_context(&local_ctx, &MetaState::new());
    assert!(
        result.is_err(),
        "TrustSolver must reject UInt8 locals, not widen to Int"
    );
}

/// Fast-lane (TrustSolver) registration must reject Float locals (#2849 AC3).
#[test]
#[serial]
fn test_trust_solver_rejects_float_local() {
    let config = AyConfig::default().with_verify_policy(SmtVerifyPolicy::TrustSolver);
    let fvar = FVarId::new(301);
    let float_ty = Expr::const_(Name::from_string("Float"), vec![]);
    let local_ctx = vec![LocalDecl {
        fvar,
        name: "y".to_string(),
        ty: float_ty,
        value: None,
    }];
    let mut solver = create_smt_backend(&config, AyLogic::QfLra);
    let result = solver.register_fvars_from_context(&local_ctx, &MetaState::new());
    assert!(
        result.is_err(),
        "TrustSolver must reject Float locals, not widen to Real"
    );
}

#[test]
fn test_register_fvars_from_context_preserves_real_sort_without_hypothesis_entry() {
    let config = AyConfig::default().with_verify_policy(SmtVerifyPolicy::ExtractOnly);
    let real_fvar = FVarId::new(19);
    let real_expr = Expr::fvar(real_fvar);
    let real_ty = Expr::const_(Name::from_string("Real"), vec![]);
    let local_ctx = vec![LocalDecl {
        fvar: real_fvar,
        name: "x".to_string(),
        ty: real_ty.clone(),
        value: None,
    }];

    let mut solver = create_smt_backend(&config, AyLogic::QfLra);
    solver
        .register_fvars_from_context(&local_ctx, &MetaState::new())
        .expect("Real-valued locals should register on the proof-producing SMT lane");
    solver
        .translate_and_assert(&real_lt(real_expr.clone(), real_of_nat(1)))
        .expect("registered Real FVar should translate as a Real SMT symbol");

    let expected_name = "fvar_19";
    let (registered_expr, registered_ty) = solver
        .registered_var(expected_name)
        .expect("Real registration should seed the reconstruction map");
    assert!(
        matches!(registered_expr.kind(), clean_kernel::ExprKind::FVar(id) if *id == real_fvar),
        "Real registration should keep the original local expression"
    );
    assert_eq!(
        registered_ty, &real_ty,
        "Real registration should preserve Lean Real at the reconstruction boundary"
    );

    assert!(
        solver.registered_hypothesis(expected_name).is_none(),
        "term-valued Real locals should only seed back-translation, not proof hypotheses"
    );
}

#[test]
fn test_register_fvars_from_context_rejects_float_type_as_unsound_domain() {
    let config = AyConfig::default().with_verify_policy(SmtVerifyPolicy::ExtractOnly);
    let float_fvar = FVarId::new(20);
    let float_ty = Expr::const_(Name::from_string("Float"), vec![]);
    let local_ctx = vec![LocalDecl {
        fvar: float_fvar,
        name: "f".to_string(),
        ty: float_ty.clone(),
        value: None,
    }];

    let mut solver = create_smt_backend(&config, AyLogic::QfLra);
    let err = solver
        .register_fvars_from_context(&local_ctx, &MetaState::new())
        .expect_err("Float locals must be rejected: IEEE 754 semantics differ from SMT Real");

    assert!(
        matches!(err, AyError::UnsupportedExpr(ref msg) if msg.contains("unsupported SMT local declaration type")),
        "Float rejection should produce UnsupportedExpr, got: {err:?}"
    );

    let expected_name = "fvar_20";
    assert!(
        solver.registered_var(expected_name).is_none(),
        "rejected Float should not seed a phantom back-translation entry"
    );
    assert!(
        solver.registered_hypothesis(expected_name).is_none(),
        "rejected Float should not seed a phantom hypothesis-proof entry"
    );
}

#[test]
fn test_register_fvars_from_context_keeps_int_sort_for_integer_locals() {
    let config = AyConfig::default().with_verify_policy(SmtVerifyPolicy::ExtractOnly);
    let int_fvar = FVarId::new(21);
    let int_expr = Expr::fvar(int_fvar);
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let local_ctx = vec![LocalDecl {
        fvar: int_fvar,
        name: "n".to_string(),
        ty: int_ty.clone(),
        value: None,
    }];

    let mut solver = create_smt_backend(&config, AyLogic::QfLia);
    solver
        .register_fvars_from_context(&local_ctx, &MetaState::new())
        .expect("Int-valued locals should keep the Int SMT registration path");
    solver
        .translate_and_assert(&int_le(int_expr.clone(), Expr::nat_lit(1)))
        .expect("registered Int FVar should translate through the integer SMT lane");

    let expected_name = "fvar_21";
    let (registered_expr, registered_ty) = solver
        .registered_var(expected_name)
        .expect("Int registration should seed the reconstruction map");
    assert_eq!(
        registered_expr, &int_expr,
        "Int registration should keep the original local expression"
    );
    assert_eq!(
        registered_ty, &int_ty,
        "Int registration should stay Lean Int after the Real widening"
    );
}
