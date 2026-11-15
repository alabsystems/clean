// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Public-entry regressions for memo reuse at equal-depth, different scopes.
//!
//! The malformed fixtures deliberately violate the declared-FVar precondition.
//! They test consistent rejection, not an exploit of a well-scoped program or
//! acceptance of a false certified theorem. No private memo frame, fabricated
//! entry, environment axiom, or inference-mode override is used here.

use clean_kernel::cert::CertVerifier;
use clean_kernel::expr::{ExprKind, FVarId, MDataMap};
use clean_kernel::{BinderInfo, Environment, Expr, TypeChecker, TypeError};
use std::sync::Arc;

fn metadata(inner: Expr) -> Arc<Expr> {
    Arc::new(Expr::from_kind(ExprKind::MData(
        MDataMap::new(),
        Arc::new(inner),
    )))
}

fn body(inner: Expr, application: bool) -> Arc<Expr> {
    let shared = metadata(inner);
    if application {
        // This function ignores its argument, but full checking and retained
        // certificate inference must still infer the actual shared argument.
        let function = Arc::new(Expr::lam(BinderInfo::Default, Expr::prop(), Expr::prop()));
        Arc::new(Expr::app_arc(function, shared))
    } else {
        shared
    }
}

fn malformed(application: bool) -> Expr {
    let shared = body(Expr::fvar(FVarId::new(0)), application);
    let domain = Arc::new(Expr::pi_arc(
        BinderInfo::Default,
        Arc::new(Expr::prop()),
        shared.clone(),
    ));
    // The inner Pi introduces FVar0, infers the shared child, and pops it.
    // The outer Pi then introduces a DIFFERENT FVar at the same depth.
    // Retaining an Arc does not retain the old variable's scope.
    Expr::pi_arc(BinderInfo::Default, domain, shared)
}

fn well_scoped(application: bool) -> Expr {
    let product = Arc::new(Expr::pi_arc(
        BinderInfo::Default,
        Arc::new(Expr::prop()),
        body(Expr::bvar(0), application),
    ));
    // Unlike the malformed raw FVar, each local BVar is opened afresh under
    // its OWN Pi. Reusing this whole closed product is well-scoped in both
    // positions. Merely substituting BVar0 in `malformed` is not this control:
    // that outer body would name a proof, not necessarily a type.
    Expr::pi_arc(BinderInfo::Default, product.clone(), product)
}

fn expected_type(application: bool) -> Expr {
    if application {
        Expr::type_()
    } else {
        Expr::prop()
    }
}

fn checker(env: &Environment, cached: bool) -> TypeChecker<'_> {
    let mut checker = TypeChecker::new(env);
    if !cached {
        checker.set_max_cache_entries(0);
    }
    checker
}

fn assert_unknown_fvar<T: std::fmt::Debug>(result: Result<T, TypeError>) {
    assert!(
        matches!(&result, Err(TypeError::UnknownFVar(id)) if *id == FVarId::new(0)),
        "the retired FVar must be rejected, got {result:?}"
    );
}

fn assert_recovered(checker: &TypeChecker<'_>) {
    assert_eq!(checker.local_context_len(), 0);
    assert_eq!(
        checker
            .infer_type_full(&Expr::prop())
            .expect("subsequent inference"),
        Expr::type_()
    );
    assert_eq!(checker.local_context_len(), 0);
}

#[test]
fn full_inference_rejects_retired_metadata_fvar_with_or_without_cache() {
    let env = Environment::new();
    for cached in [false, true] {
        let checker = checker(&env, cached);
        assert_unknown_fvar(checker.infer_type_full(&malformed(false)));
        assert_recovered(&checker);
    }
}

#[test]
fn full_application_check_rejects_retired_fvar_with_or_without_cache() {
    let env = Environment::new();
    for cached in [false, true] {
        // Fresh checkers give both public entry points the same initial IDs.
        let inference = checker(&env, cached);
        assert_unknown_fvar(inference.infer_type_full(&malformed(true)));
        assert_recovered(&inference);
        let checking = checker(&env, cached);
        assert_unknown_fvar(checking.check_type(&malformed(true), &Expr::type_()));
        assert_recovered(&checking);
    }
}

#[test]
fn retained_inference_rejects_retired_fvar_with_or_without_cache() {
    let env = Environment::new();
    for application in [false, true] {
        for cached in [false, true] {
            let checker = checker(&env, cached);
            // The application case exercises the existing certificate Arc
            // memo, not only the newer release metadata-child memo.
            assert_unknown_fvar(checker.infer_type_with_cert(&malformed(application)));
            assert_recovered(&checker);
        }
    }
}

#[test]
fn shared_bound_variables_preserve_full_checking_and_cache_parity() {
    let env = Environment::new();
    for application in [false, true] {
        let term = well_scoped(application);
        let expected = expected_type(application);
        for cached in [false, true] {
            let checker = checker(&env, cached);
            assert_eq!(
                checker.infer_type_full(&term).expect("well-scoped type"),
                expected
            );
            checker
                .check_type(&term, &expected)
                .expect("well-scoped full check");
            assert_recovered(&checker);
        }
    }
}

#[test]
fn shared_bound_variable_certificates_replay_with_or_without_cache() {
    let env = Environment::new();
    for application in [false, true] {
        let term = well_scoped(application);
        let expected = expected_type(application);
        for cached in [false, true] {
            let checker = checker(&env, cached);
            let (ty, certificate) = checker
                .infer_type_with_cert(&term)
                .expect("retained derivation");
            assert_eq!(ty, expected);
            assert_eq!(
                CertVerifier::new(&env)
                    .verify(&certificate, &term)
                    .expect("independent replay"),
                expected
            );
            assert_recovered(&checker);
        }
    }
}
