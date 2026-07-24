// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::super::ay_solver::create_smt_backend;
use super::super::ay_solver_translation::register_exists_witness_bindings;
use super::super::*;
use super::exists_support::*;
use crate::tactic::smt_translate::ExistsSkolemization;
use crate::tactic::LocalDecl;
use crate::unify::MetaState;
use clean_auto::bridge::ay_contract::{AyError, AyLogic, VariableMapping};
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, Level, Name};
use serial_test::serial;

// -- Callable FVar head registration (from ay_solver_tests.rs) --

#[test]
#[serial]
fn test_verifiable_callable_fvar_head_registers_on_first_use_and_proves_congruence_goal() {
    let config = AyConfig::default().with_verify_policy(SmtVerifyPolicy::ExtractOnly);
    let pred_fvar = FVarId::new(80);
    let x_fvar = FVarId::new(81);
    let y_fvar = FVarId::new(82);
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let pred_ty = mk_int_to_prop_type();
    let local_ctx = vec![
        LocalDecl {
            fvar: pred_fvar,
            name: "p".to_string(),
            ty: pred_ty.clone(),
            value: None,
        },
        LocalDecl {
            fvar: x_fvar,
            name: "x".to_string(),
            ty: int_ty.clone(),
            value: None,
        },
        LocalDecl {
            fvar: y_fvar,
            name: "y".to_string(),
            ty: int_ty.clone(),
            value: None,
        },
    ];

    let mut solver = create_smt_backend(&config, AyLogic::QfUflia);
    solver
        .register_fvars_from_context(&local_ctx, &MetaState::new())
        .expect("callable and scalar locals should register on the verifiable path");

    assert!(
        solver.registered_var("fvar_80").is_none(),
        "callable heads should not seed VariableMapping before their first application"
    );
    assert!(
        solver.registered_hypothesis("fvar_80").is_none(),
        "callable heads are terms, not proof hypotheses"
    );

    let x_expr = Expr::fvar(x_fvar);
    let y_expr = Expr::fvar(y_fvar);
    let pred_x = mk_fvar_app(pred_fvar, std::slice::from_ref(&x_expr));
    let pred_y = mk_fvar_app(pred_fvar, std::slice::from_ref(&y_expr));
    let eq_xy = mk_int_eq(x_expr.clone(), y_expr.clone());

    solver
        .translate_and_assert(&eq_xy)
        .expect("x = y should translate on the verifiable path");
    solver
        .translate_and_assert(&pred_x)
        .expect("p x should translate through the callable FVar head lane");

    let (registered_expr, registered_ty) = solver
        .registered_var("fvar_80")
        .expect("first callable use should seed VariableMapping for reconstruction");
    assert_eq!(
        registered_expr,
        &Expr::fvar(pred_fvar),
        "the callable head should map back to the original Lean FVar"
    );
    assert_eq!(
        registered_ty, &pred_ty,
        "the callable head should keep its original Lean function type"
    );
    assert!(
        solver.registered_hypothesis("fvar_80").is_none(),
        "callable heads must not be added to hypothesis_proofs"
    );

    let outcome = solver
        .prove(&pred_y)
        .expect("EUF congruence should prove p y from x = y and p x");
    assert!(
        outcome.proved,
        "verifiable EUF lane should accept callable FVar heads in congruence proofs"
    );
}

// -- Existential hypothesis witness binding (from ay_solver_tests.rs) --

/// Regression for #2822: existential hypotheses must allocate reconstruction-local
/// placeholders and synthetic proof entries instead of seeding raw Skolem Exprs.
#[test]
#[serial]
fn test_translate_and_assert_hypothesis_records_exists_witness_binding() {
    let config = AyConfig::default().with_verify_policy(SmtVerifyPolicy::ExtractOnly);
    let mut solver = create_smt_backend(&config, AyLogic::QfUf);
    let hyp_fvar = FVarId::new(21);
    let exists_expr = mk_exists_prop_identity();
    let local_ctx = vec![LocalDecl {
        fvar: hyp_fvar,
        name: "hex".to_string(),
        ty: exists_expr.clone(),
        value: None,
    }];

    solver
        .register_fvars_from_context(&local_ctx, &MetaState::new())
        .expect("source existential hypothesis should register in the solver context");
    solver
        .translate_and_assert_hypothesis(hyp_fvar, &exists_expr)
        .expect("existential hypothesis should assert through the witness-aware path");

    let bindings = solver.exists_witness_bindings();
    assert_eq!(bindings.len(), 1);
    let binding = &bindings[0];
    assert_eq!(binding.skolem_smt_name, "sk_exists_0");
    assert_eq!(binding.source_hyp_fvar, hyp_fvar);
    assert_eq!(binding.source_exists_proof, Expr::fvar(hyp_fvar));
    assert_eq!(binding.binder_type, Expr::prop());
    assert_eq!(
        binding.predicate,
        Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0))
    );
    assert!(
        !binding.witness_fvar.is_sentinel() && !binding.witness_proof_fvar.is_sentinel(),
        "placeholder witness/proof FVars must stay out of the sentinel range"
    );

    let (registered_expr, registered_ty) = solver
        .registered_var("sk_exists_0")
        .expect("the existential skolem should resolve to the placeholder witness FVar");
    assert_eq!(
        registered_expr,
        &Expr::fvar(binding.witness_fvar),
        "skolem names must back-translate to the reconstruction-local witness placeholder"
    );
    assert_eq!(
        registered_ty,
        &Expr::prop(),
        "Prop existential witnesses should register with their original binder type"
    );

    let (proof_fvar, proof_expr, prop_ty) = solver
        .registered_hypothesis("sk_exists_0")
        .expect("the solver must seed a synthetic proof entry for the skolemized body");
    assert_eq!(*proof_fvar, binding.witness_proof_fvar);
    assert_eq!(proof_expr, &Expr::fvar(binding.witness_proof_fvar));
    assert_eq!(
        prop_ty,
        &Expr::fvar(binding.witness_fvar),
        "the synthetic hypothesis proposition should be the instantiated body `p witness`"
    );
}

#[test]
#[serial]
fn test_prove_skips_direct_reconstruction_for_existential_goals() {
    let config = AyConfig::default().with_verify_policy(SmtVerifyPolicy::ExtractOnly);
    let mut solver = create_smt_backend(&config, AyLogic::QfUf);
    let goal = mk_exists_prop_excluded_middle();

    let outcome = solver.prove(&goal).expect(
        "the solver should still recognize the existential goal as SMT-unsat after negation",
    );

    assert!(
        outcome.proved,
        "the SMT solve itself should succeed for the tautological existential goal"
    );
    assert!(
        outcome.direct_proof().is_none(),
        "goal-side existential Skolemization must fail closed instead of claiming a direct proof"
    );
    assert!(
        solver.exists_witness_bindings().is_empty(),
        "goal translation must not synthesize hypothesis witness bindings"
    );
}

/// Regression for #2817/#2822: asserted existential hypotheses must seed the
/// reconstruction map with placeholder witness/proof locals so proof
/// reconstruction can translate `sk_exists_*` variables without leaking raw
/// Skolem constants into kernel validation.
#[test]
#[serial]
fn test_verifiable_exists_hypothesis_registers_nat_placeholder_witness() {
    let config = AyConfig::default().with_verify_policy(SmtVerifyPolicy::ExtractOnly);
    let mut solver = create_smt_backend(&config, AyLogic::QfLia);
    let hyp_fvar = FVarId::new(22);

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let body = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat_ty.clone(),
            ),
            Expr::bvar(0),
        ),
        Expr::nat_lit(5),
    );
    let predicate = Expr::lam(BinderInfo::Default, nat_ty.clone(), body);
    let exists_expr = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Exists"), vec![]), nat_ty),
        predicate,
    );
    let local_ctx = vec![LocalDecl {
        fvar: hyp_fvar,
        name: "hex_nat".to_string(),
        ty: exists_expr.clone(),
        value: None,
    }];

    solver
        .register_fvars_from_context(&local_ctx, &MetaState::new())
        .expect("source existential hypothesis should register before assertion");
    solver
        .translate_and_assert_hypothesis(hyp_fvar, &exists_expr)
        .expect(
            "verifiable path should assert existential hypotheses through the witness-aware path",
        );

    let (registered_expr, registered_ty) = solver
        .registered_var("sk_exists_0")
        .expect("sk_exists_0 must be registered in VariableMapping after Exists assertion");

    assert!(
        matches!(registered_expr.kind(), ExprKind::FVar(_)),
        "expected FVar for skolem reconstruction expression, got {:?}",
        registered_expr.kind()
    );
    if let ExprKind::FVar(fvar_id) = registered_expr.kind() {
        assert!(
            !fvar_id.is_sentinel(),
            "skolem witness FVar must not be in sentinel range, got {}",
            fvar_id.as_u64()
        );
    }

    assert_eq!(
        registered_ty,
        &Expr::const_(Name::from_string("Nat"), vec![]),
        "Nat existential placeholders should keep the original Lean binder type"
    );

    let (proof_fvar, proof_expr, prop_ty) = solver
        .registered_hypothesis("sk_exists_0")
        .expect("the skolemized body should be registered as a synthetic hypothesis");
    assert_eq!(proof_expr, &Expr::fvar(*proof_fvar));
    assert_eq!(
        prop_ty,
        &Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                    Expr::const_(Name::from_string("Nat"), vec![]),
                ),
                registered_expr.clone(),
            ),
            Expr::nat_lit(5),
        ),
        "the synthetic hypothesis proposition should be the instantiated body `Eq Nat witness 5`"
    );
}

#[test]
#[serial]
fn test_translate_and_assert_hypothesis_normalizes_nested_exists_placeholders() {
    let config = AyConfig::default().with_verify_policy(SmtVerifyPolicy::ExtractOnly);
    let mut solver = create_smt_backend(&config, AyLogic::QfLia);
    let hyp_fvar = FVarId::new(23);
    let exists_expr = mk_nested_exists_nat_eq();
    let local_ctx = vec![LocalDecl {
        fvar: hyp_fvar,
        name: "hex_nested_nat".to_string(),
        ty: exists_expr.clone(),
        value: None,
    }];

    solver
        .register_fvars_from_context(&local_ctx, &MetaState::new())
        .expect("nested existential hypothesis should register before assertion");
    solver
        .translate_and_assert_hypothesis(hyp_fvar, &exists_expr)
        .expect("nested existential hypothesis should assert through the witness-aware path");

    let bindings = solver.exists_witness_bindings();
    assert_eq!(
        bindings.len(),
        2,
        "nested Exists should record two bindings"
    );
    let outer = &bindings[0];
    let inner = &bindings[1];
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);

    assert_eq!(outer.skolem_smt_name, "sk_exists_0");
    assert_eq!(inner.skolem_smt_name, "sk_exists_1");
    assert_eq!(outer.source_hyp_fvar, hyp_fvar);
    assert_eq!(inner.source_hyp_fvar, hyp_fvar);
    assert_eq!(outer.source_exists_proof, Expr::fvar(hyp_fvar));
    assert_eq!(
        inner.source_exists_proof,
        Expr::fvar(outer.witness_proof_fvar),
        "inner replay should chain from the outer synthetic proof witness"
    );
    assert_eq!(outer.binder_type, nat_ty);
    assert_eq!(
        inner.binder_type,
        Expr::const_(Name::from_string("Nat"), vec![])
    );

    let expected_inner_predicate = Expr::lam(
        BinderInfo::Default,
        Expr::const_(Name::from_string("Nat"), vec![]),
        mk_nat_eq(Expr::fvar(outer.witness_fvar), Expr::bvar(0)),
    );
    assert_eq!(
        inner.predicate, expected_inner_predicate,
        "inner predicate should replace the translator placeholder with the outer solver witness"
    );

    assert_nested_exists_registrations(&solver, outer, inner);
}

/// Verify that both outer and inner skolem registrations carry the correct
/// witness placeholder FVars and synthetic hypothesis propositions.
fn assert_nested_exists_registrations(
    solver: &SmtSolver,
    outer: &ay_solver_types::ExistsWitnessBinding,
    inner: &ay_solver_types::ExistsWitnessBinding,
) {
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);

    let (outer_registered_expr, outer_registered_ty) = solver
        .registered_var("sk_exists_0")
        .expect("outer skolem should be back-translated to the first witness placeholder");
    assert_eq!(outer_registered_expr, &Expr::fvar(outer.witness_fvar));
    assert_eq!(outer_registered_ty, &nat_ty);

    let (_, outer_proof_expr, outer_prop_ty) = solver
        .registered_hypothesis("sk_exists_0")
        .expect("outer skolem should register the instantiated inner Exists body");
    assert_eq!(outer_proof_expr, &Expr::fvar(outer.witness_proof_fvar));
    assert_eq!(
        outer_prop_ty,
        &mk_exists_prop(
            nat_ty.clone(),
            mk_nat_eq(Expr::fvar(outer.witness_fvar), Expr::bvar(0)),
            vec![Level::zero()],
        ),
        "outer synthetic hypothesis should carry the inner Exists instantiated at the outer witness"
    );

    let (inner_registered_expr, inner_registered_ty) = solver
        .registered_var("sk_exists_1")
        .expect("inner skolem should be back-translated to the second witness placeholder");
    assert_eq!(inner_registered_expr, &Expr::fvar(inner.witness_fvar));
    assert_eq!(inner_registered_ty, &nat_ty);

    let (_, inner_proof_expr, inner_prop_ty) = solver
        .registered_hypothesis("sk_exists_1")
        .expect("inner skolem should register the fully instantiated equality body");
    assert_eq!(inner_proof_expr, &Expr::fvar(inner.witness_proof_fvar));
    assert_eq!(
        inner_prop_ty,
        &mk_nat_eq(
            Expr::fvar(outer.witness_fvar),
            Expr::fvar(inner.witness_fvar)
        ),
        "inner synthetic hypothesis should carry the normalized nested equality body"
    );
}

// -- Existential edge cases (from ay_solver_exists_tests.rs) --

#[test]
fn test_register_fvars_from_context_rejects_partially_applied_exists_hypotheses() {
    let config = AyConfig::default().with_verify_policy(SmtVerifyPolicy::ExtractOnly);
    let partial_exists = Expr::app(
        Expr::const_(Name::from_string("Exists"), vec![Level::zero()]),
        Expr::prop(),
    );
    let local_ctx = vec![LocalDecl {
        fvar: FVarId::new(31),
        name: "hpartial".to_string(),
        ty: partial_exists,
        value: None,
    }];

    let mut solver = create_smt_backend(&config, AyLogic::QfUf);
    let err = solver
        .register_fvars_from_context(&local_ctx, &MetaState::new())
        .expect_err("partially applied Exists should fail closed during local registration");

    assert!(
        matches!(err, AyError::UnsupportedExpr(ref message) if message.contains("unsupported SMT local declaration type")),
        "unexpected registration error for partially applied Exists: {err:?}"
    );
}

#[test]
fn test_register_exists_witness_bindings_rejects_malformed_source_shape() {
    let mut var_map = VariableMapping::new();
    let mut exists_bindings = Vec::new();
    let mut next_placeholder_fvar = 0;
    let partial_exists = Expr::app(
        Expr::const_(Name::from_string("Exists"), vec![Level::zero()]),
        Expr::prop(),
    );
    let skolemizations = vec![ExistsSkolemization {
        skolem_smt_name: "sk_exists_0".to_string(),
        binder_type: Expr::prop(),
        predicate: Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0)),
        translator_placeholder_fvar: FVarId::new(0),
    }];

    let err = register_exists_witness_bindings(
        &mut var_map,
        &mut exists_bindings,
        &mut next_placeholder_fvar,
        FVarId::new(32),
        &partial_exists,
        &skolemizations,
    )
    .expect_err("malformed Exists witness state should fail before any binding is recorded");

    assert!(
        matches!(err, AyError::UnsupportedExpr(ref message) if message.contains("malformed Exists witness state")),
        "unexpected binding registration error: {err:?}"
    );
    assert!(
        exists_bindings.is_empty(),
        "failed binding registration must not leave partial witness state behind"
    );
    assert!(
        var_map.get_var("sk_exists_0").is_none(),
        "failed binding registration must not seed a phantom skolem back-translation entry"
    );
    assert!(
        var_map.get_hypothesis("sk_exists_0").is_none(),
        "failed binding registration must not seed a phantom synthetic hypothesis"
    );
}

#[test]
fn test_register_exists_witness_bindings_rejects_mismatched_skolem_metadata() {
    let mut var_map = VariableMapping::new();
    let mut exists_bindings = Vec::new();
    let mut next_placeholder_fvar = 0;
    let source_exists = mk_exists_prop_identity();
    let skolemizations = vec![ExistsSkolemization {
        skolem_smt_name: "sk_exists_0".to_string(),
        binder_type: Expr::prop(),
        predicate: Expr::lam(BinderInfo::Default, Expr::prop(), mk_not(Expr::bvar(0))),
        translator_placeholder_fvar: FVarId::new(0),
    }];

    let err = register_exists_witness_bindings(
        &mut var_map,
        &mut exists_bindings,
        &mut next_placeholder_fvar,
        FVarId::new(35),
        &source_exists,
        &skolemizations,
    )
    .expect_err("mismatched skolem metadata should fail before any binding is recorded");

    assert!(
        matches!(err, AyError::UnsupportedExpr(ref message) if message.contains("source proposition no longer matches skolemization metadata")),
        "unexpected binding registration error for mismatched metadata: {err:?}"
    );
    assert!(
        exists_bindings.is_empty(),
        "metadata mismatch must not leave partial witness state behind"
    );
    assert!(
        var_map.get_var("sk_exists_0").is_none(),
        "metadata mismatch must not seed a phantom skolem back-translation entry"
    );
    assert!(
        var_map.get_hypothesis("sk_exists_0").is_none(),
        "metadata mismatch must not seed a phantom synthetic hypothesis"
    );
}
