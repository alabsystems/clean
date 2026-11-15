// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rebinding: the INFERENCE and REPLAY controls, split out of
//! `rebind_dag_tests.rs`.
//!
//! That file's own module doc already draws this line -- "the inference/replay
//! controls use closed terms in an empty environment" -- and the split is
//! mechanical along it: these cases build real terms, run `infer_type_with_cert`
//! and re-verify, where the structural fixtures next door test the
//! transformation against hand-built certificates.
//!
//! Split 2026-09-16 because `rebind_dag_tests.rs` had crossed 1000 lines (1005)
//! and `paragon-ratchet`'s `files_over_1000` is shrink-only. Nothing here
//! changed except which file the text lives in; `core_allocations` is shared
//! from the sibling module rather than duplicated, so there is still exactly one
//! definition of it.

use super::dag_tests::core_allocations;
use crate::cert::{CertError, CertVerifier, ProofCert};
use crate::env::Environment;
use crate::expr::{BinderInfo, Expr};
use crate::name::Name;
use crate::tc::TypeChecker;
use std::sync::Arc;

fn binary_prop_type() -> Expr {
    Expr::pi(
        BinderInfo::Default,
        Expr::prop(),
        Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
    )
}

fn shared_expr(depth: u32, function_idx: u32, leaf_idx: u32) -> Arc<Expr> {
    let function = Arc::new(Expr::bvar(function_idx));
    let mut node = Arc::new(Expr::bvar(leaf_idx));
    for _ in 0..depth {
        let applied = Arc::new(Expr::app_arc(function.clone(), node.clone()));
        node = Arc::new(Expr::app_arc(applied, node));
    }
    node
}

fn nested_lambda(depth: u32) -> Expr {
    Expr::lam(
        BinderInfo::Default,
        binary_prop_type(),
        Expr::lam_arc(
            BinderInfo::Default,
            Arc::new(Expr::prop()),
            shared_expr(depth, 1, 0),
        ),
    )
}

fn nested_lambda_type() -> Expr {
    Expr::pi(
        BinderInfo::Default,
        binary_prop_type(),
        Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
    )
}

#[test]
fn inferred_retained_nested_binder_certificate_stays_linear_at_depth_24() {
    let env = Environment::new();
    let expr = nested_lambda(24);
    let (ty, cert) = TypeChecker::new(&env)
        .infer_type_with_cert(&expr)
        .expect("closed shared lambda");
    assert_eq!(ty, nested_lambda_type());
    let allocations = core_allocations(&cert);
    assert!(
        allocations <= 16 * 24 + 64,
        "allocated {allocations} certificate nodes"
    );
    // The verifier is deliberately exercised on bounded depth below; it has
    // its own traversal and is not claimed to share this new memo.
}

#[test]
fn inferred_retained_lam_pi_let_and_dependent_certificates_replay() {
    let env = Environment::new();
    let lambda = nested_lambda(4);
    let pi = Expr::pi(
        BinderInfo::Default,
        binary_prop_type(),
        Expr::pi_arc(
            BinderInfo::Default,
            Arc::new(Expr::prop()),
            shared_expr(4, 1, 0),
        ),
    );
    let with_let = Expr::lam(
        BinderInfo::Default,
        binary_prop_type(),
        Expr::lam(
            BinderInfo::Default,
            Expr::prop(),
            Expr::let_named_arc(
                Name::from_string("saved"),
                Arc::new(Expr::prop()),
                Arc::new(Expr::bvar(0)),
                shared_expr(4, 2, 0),
                false,
            ),
        ),
    );
    let dependent = Expr::lam(
        BinderInfo::Default,
        Expr::type_(),
        Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
    );
    let dependent_type = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
    );
    for (expr, expected) in [
        (lambda, nested_lambda_type()),
        (pi, Expr::prop()),
        (with_let, nested_lambda_type()),
        (dependent, dependent_type),
    ] {
        let (ty, cert) = TypeChecker::new(&env)
            .infer_type_with_cert(&expr)
            .expect("closed inference");
        assert_eq!(ty, expected);
        let checked = CertVerifier::new(&env)
            .verify(&cert, &expr)
            .expect("independent certificate replay");
        assert_eq!(checked, expected);
    }
}

#[test]
fn inferred_rebound_certificate_rejects_corruption_at_the_same_claim() {
    let env = Environment::new();
    let expr = Expr::lam(
        BinderInfo::Default,
        Expr::type_(),
        Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
    );
    let expected = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
    );
    let (ty, good) = TypeChecker::new(&env)
        .infer_type_with_cert(&expr)
        .expect("dependent identity");
    assert_eq!(ty, expected);
    let mut verifier = CertVerifier::new(&env);
    assert_eq!(
        verifier.verify(&good, &expr).expect("positive replay"),
        expected
    );
    for corrupt_type in [false, true] {
        let mut bad = good.clone();
        let ProofCert::Lam {
            body_cert: outer, ..
        } = &mut bad
        else {
            panic!("outer Lam")
        };
        let ProofCert::Lam {
            body_cert: inner, ..
        } = Arc::make_mut(outer)
        else {
            panic!("inner Lam")
        };
        let ProofCert::BVar { idx, expected_type } = Arc::make_mut(inner) else {
            panic!("BVar")
        };
        if corrupt_type {
            **expected_type = Expr::prop();
            assert!(matches!(
                verifier.verify(&bad, &expr),
                Err(CertError::TypeMismatch { .. })
            ));
        } else {
            *idx = 1;
            assert!(matches!(
                verifier.verify(&bad, &expr),
                Err(CertError::InvalidBVar(0))
            ));
        }
        // The same expression and independently authored target remain fixed,
        // and a refusal must leave the verifier's binder context reusable.
        assert_eq!(
            verifier.verify(&good, &expr).expect("replay after refusal"),
            expected
        );
    }
}
