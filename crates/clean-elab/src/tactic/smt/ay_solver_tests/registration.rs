// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::super::ay_solver::create_smt_backend;
use super::super::*;
use crate::tactic::LocalDecl;
use crate::unify::MetaState;
use clean_auto::bridge::ay_contract::{AyError, AyLogic};
use clean_kernel::{Expr, FVarId, Name};
use serial_test::serial;

// -- Prop registration and synchronization --

#[test]
#[serial]
fn test_verifiable_paths_keep_variable_mapping_registration_in_sync() {
    let config = AyConfig::default().with_verify_policy(SmtVerifyPolicy::ExtractOnly);
    let prop_fvar = FVarId::new(42);
    let prop_expr = Expr::fvar(prop_fvar);
    let local_ctx = vec![LocalDecl {
        fvar: prop_fvar,
        name: "p".to_string(),
        ty: Expr::prop(),
        value: None,
    }];

    let mut solver = create_smt_backend(&config, AyLogic::QfUf);
    solver
        .register_fvars_from_context(&local_ctx, &MetaState::new())
        .expect("Prop-typed local should register");
    solver
        .translate_and_assert(&prop_expr)
        .expect("assert path should translate a registered Prop FVar");
    let (assert_expr, assert_ty) = solver
        .registered_var("fvar_42")
        .expect("assert path should preserve var_map registration from context");
    assert_eq!(
        assert_expr, &prop_expr,
        "assert path should retain the source proposition expression"
    );
    assert_eq!(
        assert_ty,
        &Expr::prop(),
        "Bool SMT declarations should register back as Lean propositions"
    );

    let prove_outcome = solver
        .prove(&prop_expr)
        .expect("goal path should still solve after reusing the synchronized translation state");
    assert!(
        prove_outcome.proved,
        "the goal path should prove the asserted proposition after reusing the shared sync helper"
    );
    let (prove_expr, prove_ty) = solver
        .registered_var("fvar_42")
        .expect("goal path should preserve var_map registration across prove");
    assert_eq!(
        prove_expr, &prop_expr,
        "goal path should preserve the registered source proposition expression"
    );
    assert_eq!(
        prove_ty,
        &Expr::prop(),
        "goal path should preserve Bool SMT registrations as Lean propositions"
    );
}

#[test]
#[serial]
fn test_register_fvars_from_context_reuses_translator_owned_name_for_prop_fvars() {
    let config = AyConfig::default().with_verify_policy(SmtVerifyPolicy::ExtractOnly);
    let prop_fvar = FVarId::new(17);
    let prop_expr = Expr::fvar(prop_fvar);
    let local_ctx = vec![LocalDecl {
        fvar: prop_fvar,
        name: "p".to_string(),
        ty: Expr::prop(),
        value: None,
    }];

    let mut solver = create_smt_backend(&config, AyLogic::QfUf);
    solver
        .register_fvars_from_context(&local_ctx, &MetaState::new())
        .expect("Prop-valued local declarations should register before translation");
    solver
        .translate_and_assert(&prop_expr)
        .expect("registered Prop FVar should translate as a Bool SMT symbol");

    let expected_name = "fvar_17";
    let (registered_expr, registered_ty) = solver
        .registered_var(expected_name)
        .expect("register_fvars_from_context should seed the reconstruction map");
    assert_eq!(
        registered_expr, &prop_expr,
        "the reconstruction map should keep the original Prop FVar expression"
    );
    assert_eq!(
        registered_ty,
        &Expr::prop(),
        "Prop-valued FVars should stay Bool-sorted at the reconstruction boundary"
    );

    let (hyp_fvar, hyp_expr, hyp_ty) = solver
        .registered_hypothesis(expected_name)
        .expect("hypothesis proof mapping should reuse the same SMT symbol");
    assert_eq!(
        *hyp_fvar, prop_fvar,
        "hypothesis registration should point back to the original local declaration"
    );
    assert_eq!(
        hyp_expr, &prop_expr,
        "hypothesis registration should keep the local proof witness expression"
    );
    assert_eq!(
        hyp_ty,
        &Expr::prop(),
        "hypothesis registration should preserve the proposition type"
    );
}

// -- Sort-valued and unsupported local skips --

#[test]
fn test_register_fvars_from_context_skips_sort_valued_locals_without_seeding_maps() {
    let config = AyConfig::default().with_verify_policy(SmtVerifyPolicy::ExtractOnly);
    let sort_fvar = FVarId::new(18);
    let local_ctx = vec![LocalDecl {
        fvar: sort_fvar,
        name: "A".to_string(),
        ty: Expr::type_(),
        value: None,
    }];

    let mut solver = create_smt_backend(&config, AyLogic::QfUf);
    solver
        .register_fvars_from_context(&local_ctx, &MetaState::new())
        .expect("sort-valued locals should be ignored during SMT registration");

    let expected_name = "fvar_18";
    assert!(
        solver.registered_var(expected_name).is_none(),
        "sort-valued locals should not seed term back-translation entries"
    );
    assert!(
        solver.registered_hypothesis(expected_name).is_none(),
        "sort-valued locals should not seed hypothesis-proof entries"
    );
}

#[test]
#[serial]
fn test_register_fvars_from_context_rejects_uint8_wrapping_goal_locals() {
    let config = AyConfig::default().with_verify_policy(SmtVerifyPolicy::ExtractOnly);
    let uint8_fvar = FVarId::new(19);
    let uint8_ty = Expr::const_(Name::from_string("UInt8"), vec![]);
    let local_ctx = vec![LocalDecl {
        fvar: uint8_fvar,
        name: "x".to_string(),
        ty: uint8_ty.clone(),
        value: None,
    }];

    // Motivating unsound case from #2846: `x + 1 > x` for `x : UInt8`.
    // Registration must fail closed before translation can widen the bounded
    // modular domain into unbounded SMT Int arithmetic.

    let mut solver = create_smt_backend(&config, AyLogic::QfLia);
    let err = solver
        .register_fvars_from_context(&local_ctx, &MetaState::new())
        .expect_err("UInt8 locals must be rejected before any wrapping arithmetic is translated");

    assert!(
        matches!(
            err,
            AyError::UnsupportedExpr(ref msg)
                if msg.contains("unsupported SMT local declaration type")
                    && msg.contains("UInt8")
        ),
        "UInt8 registration should fail closed with an unsupported-type diagnostic, got: {err:?}"
    );

    let expected_name = "fvar_19";
    assert!(
        solver.registered_var(expected_name).is_none(),
        "rejected UInt8 locals must not seed phantom reconstruction entries"
    );
    assert!(
        solver.registered_hypothesis(expected_name).is_none(),
        "rejected UInt8 locals must not seed phantom hypothesis mappings"
    );
}

#[test]
fn test_register_fvars_from_context_rejects_unsupported_non_sort_local_types() {
    let config = AyConfig::default().with_verify_policy(SmtVerifyPolicy::ExtractOnly);
    let string_fvar = FVarId::new(22);
    let local_ctx = vec![LocalDecl {
        fvar: string_fvar,
        name: "s".to_string(),
        ty: Expr::const_(Name::from_string("String"), vec![]),
        value: None,
    }];

    let mut solver = create_smt_backend(&config, AyLogic::QfUf);
    let err = solver
        .register_fvars_from_context(&local_ctx, &MetaState::new())
        .expect_err("unsupported non-sort locals must fail closed during SMT registration");

    assert!(
        matches!(err, AyError::UnsupportedExpr(ref message) if message.contains("unsupported SMT local declaration type")),
        "unexpected registration error for unsupported local type: {err:?}"
    );

    let expected_name = "fvar_22";
    assert!(
        solver.registered_var(expected_name).is_none(),
        "failed registration should not seed a phantom back-translation entry"
    );
    assert!(
        solver.registered_hypothesis(expected_name).is_none(),
        "failed registration should not seed a phantom hypothesis-proof entry"
    );
}
