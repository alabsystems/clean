// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Direct certificate-verifier regressions for quotient reduction custody.
//!
//! The inner certificate proves only `B.f = B.f`. The conversion to a
//! `Quot.lift` application is supplied manually, including in the negative
//! cases: a certificate producer refusing to build it cannot pass these tests.

use std::sync::Arc;

use crate::cert::builder::CertBuilder;
use crate::cert::{CertError, CertVerifier, ProofCert};
use crate::env::{ConstantInfo, ConstantKind, Environment, Reducibility};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::inductive::{Constructor, InductiveDecl, InductiveType};
use crate::level::Level;
use crate::name::Name;
use crate::quot::{quot_lift_type, quot_mk_type, quot_type};

fn n(name: &str) -> Name {
    Name::from_string(name)
}

fn c(name: &str) -> Expr {
    Expr::const_(n(name), vec![])
}

fn one() -> Level {
    Level::succ(Level::zero())
}

fn base_environment() -> Environment {
    let mut env = Environment::new();
    env.init_eq().expect("native Eq");
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: n("B"),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: n("B.t"),
                    type_: c("B"),
                },
                Constructor {
                    name: n("B.f"),
                    type_: c("B"),
                },
            ],
        }],
    })
    .expect("native two-constructor B");
    env
}

fn eq_b(left: Expr, right: Expr) -> Expr {
    [c("B"), left, right]
        .into_iter()
        .fold(Expr::const_(n("Eq"), vec![one()]), Expr::app)
}

fn identity_b() -> Expr {
    Expr::lam(BinderInfo::Default, c("B"), Expr::bvar(0))
}

fn lift_on_mk(relation: Expr, respect: Expr) -> Expr {
    let mk = [c("B"), relation.clone(), c("B.f")]
        .into_iter()
        .fold(Expr::const_(n("Quot.mk"), vec![one()]), Expr::app);
    [c("B"), relation, c("B"), identity_b(), respect, mk]
        .into_iter()
        .fold(Expr::const_(n("Quot.lift"), vec![one(), one()]), Expr::app)
}

/// Identity respects equality by returning the supplied equality proof.
fn honest_lift() -> Expr {
    let equality = eq_b(Expr::bvar(1), Expr::bvar(0));
    let relation = Expr::lam(
        BinderInfo::Default,
        c("B"),
        Expr::lam(BinderInfo::Default, c("B"), equality.clone()),
    );
    let respect = Expr::lam(
        BinderInfo::Default,
        c("B"),
        Expr::lam(
            BinderInfo::Default,
            c("B"),
            Expr::lam(BinderInfo::Default, equality, Expr::bvar(0)),
        ),
    );
    lift_on_mk(relation, respect)
}

fn replace_pi_domain(ty: &Expr, index: usize, replacement: Expr) -> Expr {
    let ExprKind::Pi(binder, domain, body) = &ty.kind else {
        panic!("fixture must contain the requested Pi binder");
    };
    if index == 0 {
        Expr::pi(*binder, replacement, body.as_ref().clone())
    } else {
        Expr::pi(
            *binder,
            domain.as_ref().clone(),
            replace_pi_domain(body, index - 1, replacement),
        )
    }
}

fn file_typed_environment(forge_respect: bool) -> Environment {
    let mut env = base_environment();
    let (u, v) = (n("u"), n("v"));
    let mut lift_type = quot_lift_type(&u, &v);
    if forge_respect {
        // Mirror the imported-family attack: replace h's respect obligation
        // by beta -> beta. Under alpha/r/beta/f, beta is de Bruijn index 1.
        lift_type = replace_pi_domain(
            &lift_type,
            4,
            Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::bvar(2)),
        );
    }
    let records = [
        ("Quot", vec![u.clone()], quot_type(&u)),
        ("Quot.mk", vec![u.clone()], quot_mk_type(&u)),
        ("Quot.lift", vec![u, v], lift_type),
    ]
    .into_iter()
    .map(|(name, levels, ty)| {
        ConstantInfo::new_with_reducibility(
            n(name),
            levels,
            ty,
            None,
            Reducibility::Regular(0),
            ConstantKind::Axiom,
        )
    });
    // SOUNDNESS: test-only adversarial import fixture, matching the structural
    // constant-record route in env/imported_family_tests.rs. No Quot registry
    // entry is installed, and no imported axiom is claimed to be a theorem.
    assert!(env.extend_constants_structural(records).is_empty());
    assert!(env.get_quot(&n("Quot.lift")).is_none());
    env
}

fn assert_lift_certificate_conversion(env: &Environment, lift: Expr, canonical: bool) {
    // Both the genuine application and the file-typed attack are well-typed
    // under their own declarations; rejection must not be a malformed fixture.
    assert_eq!(
        crate::tc::TypeChecker::new(env)
            .infer_type_full(&lift)
            .expect("well-typed lift application"),
        c("B")
    );

    let mut builder = CertBuilder::new(env);
    let refl = builder.const_(n("Eq.refl"), vec![one()]).expect("Eq.refl");
    let b = builder.const_(n("B"), vec![]).expect("B");
    let f = builder.const_(n("B.f"), vec![]).expect("B.f");
    let refl_b = builder.app(refl, b).expect("Eq.refl B");
    let root = builder.app(refl_b, f).expect("Eq.refl B B.f");
    let inner = builder.finish(root).expect("reflexivity certificate");
    let proof = Expr::app(
        Expr::app(Expr::const_(n("Eq.refl"), vec![one()]), c("B")),
        c("B.f"),
    );
    let actual = eq_b(c("B.f"), c("B.f"));
    let expected = eq_b(lift.clone(), c("B.f"));
    let mut verifier = CertVerifier::new(env);
    assert_eq!(
        verifier.verify(&inner, &proof).expect("valid inner"),
        actual
    );
    assert!(!verifier.def_eq(&c("B.f"), &c("B.t")));

    // Intentionally NOT generated by CertBuilder/TypeChecker: the verifier
    // itself must accept or refuse the requested quotient conversion.
    let certificate = ProofCert::DefEq {
        inner: Arc::new(inner),
        expected_type: Box::new(expected.clone()),
        actual_type: Box::new(actual.clone()),
        eq_steps: vec![],
    };
    if canonical {
        assert!(env.get_quot(&n("Quot.lift")).is_some());
        assert_eq!(verifier.whnf(&lift), c("B.f"));
        assert_eq!(
            verifier
                .verify(&certificate, &proof)
                .expect("canonical quotient conversion"),
            expected
        );
    } else {
        let error = verifier
            .verify(&certificate, &proof)
            .expect_err("a name and type alone grant no quotient reduction");
        assert!(
            matches!(error, CertError::DefEqFailed { ref left, ref right }
                if left.as_ref() == &actual && right.as_ref() == &expected),
            "must refuse the exact outer conversion, not the valid inner certificate: {error}"
        );
        assert_eq!(verifier.whnf(&lift), lift, "file axiom must stay opaque");
    }
}

#[test]
fn test_cert_quot_lift_canonical_primitive_replays_conversion() {
    let mut env = base_environment();
    env.init_quot();
    assert_lift_certificate_conversion(&env, honest_lift(), true);
}

#[test]
fn test_cert_quot_lift_forged_file_type_refuses_conversion() {
    let env = file_typed_environment(true);
    let universal_relation = Expr::lam(
        BinderInfo::Default,
        c("B"),
        Expr::lam(BinderInfo::Default, c("B"), eq_b(c("B.t"), c("B.t"))),
    );
    assert_lift_certificate_conversion(&env, lift_on_mk(universal_relation, identity_b()), false);
}

#[test]
fn test_cert_quot_lift_canonical_file_type_without_primitive_refuses_conversion() {
    let env = file_typed_environment(false);
    assert_lift_certificate_conversion(&env, honest_lift(), false);
}
