// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Cubical type theory certificate tests

use crate::cert::*;
use crate::env::Environment;
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::mode::CleanMode;
use crate::TypeChecker;

fn empty_env() -> Environment {
    Environment::new()
}

fn env_with_base_prop_axiom() -> Environment {
    use crate::env::Declaration;
    use crate::name::Name;

    let mut env = Environment::new();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("base_prop"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("base_prop axiom should register");
    env
}

#[test]
fn test_cubical_interval_cert_roundtrip() {
    let env = empty_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);
    let (ty, cert) = tc
        .infer_type_with_cert(&Expr::from_kind(ExprKind::CubicalInterval))
        .unwrap();

    let mut verifier = CertVerifier::with_mode(&env, CleanMode::Cubical);
    let verified_ty = verifier
        .verify(&cert, &Expr::from_kind(ExprKind::CubicalInterval))
        .unwrap();
    assert_eq!(ty, verified_ty);
}

#[test]
fn test_cubical_endpoint_cert_roundtrip() {
    let env = empty_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    for endpoint in [
        Expr::from_kind(ExprKind::CubicalI0),
        Expr::from_kind(ExprKind::CubicalI1),
    ] {
        let (ty, cert) = tc.infer_type_with_cert(&endpoint).unwrap();
        let mut verifier = CertVerifier::with_mode(&env, CleanMode::Cubical);
        let verified_ty = verifier.verify(&cert, &endpoint).unwrap();
        assert_eq!(ty, verified_ty);
    }
}

#[test]
fn test_cubical_path_type_cert_roundtrip() {
    let env = empty_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // A : I -> Type0 (represented as λ i : I, Type0)
    let type0 = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));
    let ty_family = Expr::lam(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::CubicalInterval),
        type0,
    );

    // Prop : Type0, so it's a valid endpoint for a constant Type0 family.
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let path_ty = Expr::from_kind(ExprKind::CubicalPath {
        ty: ty_family.into(),
        left: prop.clone().into(),
        right: prop.into(),
    });

    let (ty, cert) = tc.infer_type_with_cert(&path_ty).unwrap();
    let mut verifier = CertVerifier::with_mode(&env, CleanMode::Cubical);
    let verified_ty = verifier.verify(&cert, &path_ty).unwrap();
    assert_eq!(ty, verified_ty);
}

#[test]
fn test_cubical_path_lam_and_app_cert_roundtrip() {
    let env = empty_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    // Constant path at Prop (doesn't use the interval variable).
    let path_lam = Expr::from_kind(ExprKind::CubicalPathLam {
        body: Expr::from_kind(ExprKind::Sort(Level::zero())).into(),
    });
    let (lam_ty, lam_cert) = tc.infer_type_with_cert(&path_lam).unwrap();

    let mut verifier = CertVerifier::with_mode(&env, CleanMode::Cubical);
    let verified_lam_ty = verifier.verify(&lam_cert, &path_lam).unwrap();
    assert_eq!(lam_ty, verified_lam_ty);

    // Apply the path to 0.
    let path_app = Expr::from_kind(ExprKind::CubicalPathApp {
        path: path_lam.clone().into(),
        arg: Expr::from_kind(ExprKind::CubicalI0).into(),
    });
    let (app_ty, app_cert) = tc.infer_type_with_cert(&path_app).unwrap();

    let verified_app_ty = verifier.verify(&app_cert, &path_app).unwrap();
    assert_eq!(app_ty, verified_app_ty);
}

// ========================================================================
// Tests targeting surviving mutations
// ========================================================================

// --- CertVerifier::def_eq tests ---

#[test]
fn test_cubical_hcomp_cert_rejects_non_interval_phi() {
    let env = empty_env();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let ty = Expr::type_();
    let phi = Expr::prop();
    let u = Expr::lam(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::CubicalInterval),
        Expr::prop(),
    );
    let base = Expr::prop();

    let (_, ty_cert) = tc.infer_type_with_cert(&ty).unwrap();
    let (_, phi_cert) = tc.infer_type_with_cert(&phi).unwrap();
    let (_, u_cert) = tc.infer_type_with_cert(&u).unwrap();
    let (_, base_cert) = tc.infer_type_with_cert(&base).unwrap();

    let hcomp = Expr::from_kind(ExprKind::CubicalHComp {
        ty: ty.clone().into(),
        phi: phi.into(),
        u: u.into(),
        base: base.into(),
    });

    let forged = ProofCert::CubicalHComp {
        ty_cert: Box::new(ty_cert),
        phi_cert: Box::new(phi_cert),
        u_cert: Box::new(u_cert),
        base_cert: Box::new(base_cert),
        result_type: Box::new(ty),
    };

    let mut verifier = CertVerifier::with_mode(&env, CleanMode::Cubical);
    let err = verifier
        .verify(&forged, &hcomp)
        .expect_err("hcomp cert with non-interval phi should fail");
    assert!(
        matches!(err, CertError::TypeMismatch { ref location, .. } if location == "CubicalHComp phi"),
        "expected CubicalHComp phi type mismatch, got: {err}"
    );
}

#[test]
fn test_cubical_transp_cert_rejects_wrong_result_type() {
    use crate::name::Name;

    let env = env_with_base_prop_axiom();
    let tc = TypeChecker::with_mode(&env, CleanMode::Cubical);

    let ty_family = Expr::lam(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::CubicalInterval),
        Expr::prop(),
    );
    let phi = Expr::from_kind(ExprKind::CubicalI0);
    let base = Expr::const_(Name::from_string("base_prop"), vec![]);

    let (_, ty_cert) = tc.infer_type_with_cert(&ty_family).unwrap();
    let (_, phi_cert) = tc.infer_type_with_cert(&phi).unwrap();
    let (_, base_cert) = tc.infer_type_with_cert(&base).unwrap();

    let transp = Expr::from_kind(ExprKind::CubicalTransp {
        ty: ty_family.into(),
        phi: phi.into(),
        base: base.into(),
    });

    let forged = ProofCert::CubicalTransp {
        ty_cert: Box::new(ty_cert),
        phi_cert: Box::new(phi_cert),
        base_cert: Box::new(base_cert),
        // Deliberately wrong: expected ty i1 (def-eq to Prop), not Type.
        result_type: Box::new(Expr::type_()),
    };

    let mut verifier = CertVerifier::with_mode(&env, CleanMode::Cubical);
    let err = verifier
        .verify(&forged, &transp)
        .expect_err("transp cert with wrong result type should fail");
    assert!(
        matches!(err, CertError::TypeMismatch { ref location, .. } if location == "CubicalTransp result"),
        "expected CubicalTransp result mismatch, got: {err}"
    );
}
