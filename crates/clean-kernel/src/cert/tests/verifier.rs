// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for `CertVerifier::verify` — the trusted certificate checker.
//!
//! Covers the five most common derivation step types (Sort, Pi, Lam, App, Let)
//! plus Const, Lit, FVar, BVar, and DefEq, with both happy-path and error-path
//! tests. See `verifier_extended.rs` for Sort/BVar/FVar/Lit gap-fill, MData,
//! and Proj tests.
//!
//! Part of #2435.

use crate::cert::*;
use crate::env::Declaration;
use crate::env::Environment;
use crate::expr::{BigNat, BinderInfo, Expr, ExprKind, FVarId, Literal};
use crate::level::Level;
use crate::name::Name;
use std::sync::Arc;

fn empty_env() -> Environment {
    Environment::new()
}

/// Environment with a simple axiom `MyConst : Prop`
fn env_with_const() -> Environment {
    let mut env = Environment::new();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("MyConst"),
        level_params: vec![],
        type_: Expr::from_kind(ExprKind::Sort(Level::zero())),
    })
    .expect("add MyConst axiom");
    env
}

/// Environment with a polymorphic axiom `MyPoly.{u} : Sort u`
fn env_with_poly_const() -> Environment {
    let mut env = Environment::new();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("MyPoly"),
        level_params: vec![Name::from_string("u")],
        type_: Expr::from_kind(ExprKind::Sort(Level::param(Name::from_string("u")))),
    })
    .expect("add MyPoly axiom");
    env
}

// =========================================================================
// App verification
// =========================================================================

#[test]
fn test_verify_app_basic() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    // Build: (λ (x : Prop). x) p, where p is an FVar of type Prop
    // λ (x : Prop). x : Prop → Prop (non-dependent)
    // p : Prop, so application is well-typed
    // Result type: Prop (body type of Pi instantiated with p = Prop)
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let fvar_p = FVarId(100);
    verifier.register_fvar(fvar_p, prop.clone()).unwrap();

    let id_fn = Expr::lam(
        BinderInfo::Default,
        prop.clone(),
        Expr::from_kind(ExprKind::BVar(0)),
    );
    let p_expr = Expr::from_kind(ExprKind::FVar(fvar_p));
    let app_expr = Expr::app(id_fn, p_expr.clone());

    // Certificate for the identity function λ (x : Prop). x
    let id_cert = ProofCert::Lam {
        binder_info: BinderInfo::Default,
        arg_type_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        body_cert: Box::new(ProofCert::BVar {
            idx: 0,
            expected_type: Box::new(prop.clone()),
        }),
        result_type: Box::new(Expr::pi(BinderInfo::Default, prop.clone(), prop.clone())),
    };

    // Certificate for FVar(p) : Prop
    let arg_cert = ProofCert::FVar {
        id: fvar_p,
        type_: Box::new(prop.clone()),
    };

    // App certificate: result type = Prop (from Pi codomain instantiated)
    let cert = ProofCert::App {
        fn_cert: Box::new(id_cert),
        fn_type: Box::new(Expr::pi(BinderInfo::Default, prop.clone(), prop.clone())),
        arg_cert: Box::new(arg_cert),
        result_type: Box::new(prop.clone()),
    };

    let ty = verifier
        .verify(&cert, &app_expr)
        .expect("App of identity to FVar(p) should verify");
    assert_eq!(ty, prop, "Result type should be Prop");
}

#[test]
fn test_verify_app_arg_type_mismatch() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    // (λ (x : Prop). x) applied to Nat(42) — argument type mismatch
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let id_fn = Expr::lam(
        BinderInfo::Default,
        prop.clone(),
        Expr::from_kind(ExprKind::BVar(0)),
    );
    let nat_lit = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(42))));
    let app_expr = Expr::app(id_fn, nat_lit.clone());

    let id_cert = ProofCert::Lam {
        binder_info: BinderInfo::Default,
        arg_type_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        body_cert: Box::new(ProofCert::BVar {
            idx: 0,
            expected_type: Box::new(prop.clone()),
        }),
        result_type: Box::new(Expr::pi(BinderInfo::Default, prop.clone(), prop.clone())),
    };

    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
    let arg_cert = ProofCert::Lit {
        lit: Literal::Nat(BigNat::Small(42)),
        type_: Box::new(nat_type),
    };

    let cert = ProofCert::App {
        fn_cert: Box::new(id_cert),
        fn_type: Box::new(Expr::pi(BinderInfo::Default, prop.clone(), prop.clone())),
        arg_cert: Box::new(arg_cert),
        result_type: Box::new(prop),
    };

    let err = verifier.verify(&cert, &app_expr).unwrap_err();
    assert!(
        matches!(err, CertError::TypeMismatch { ref location, .. } if location.contains("App")),
        "App with wrong arg type should produce TypeMismatch at App, got: {err}"
    );
}

#[test]
fn test_verify_app_non_pi_function() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    // Apply Prop (not a function) to Prop — function type is not Pi
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let app_expr = Expr::from_kind(ExprKind::App(
        Arc::new(prop.clone()),
        Arc::new(prop.clone()),
    ));

    let cert = ProofCert::App {
        fn_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        fn_type: Box::new(Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))),
        arg_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        result_type: Box::new(prop),
    };

    let err = verifier.verify(&cert, &app_expr).unwrap_err();
    assert!(
        matches!(err, CertError::InvalidCert(ref msg) if msg.contains("Pi")),
        "App where function has non-Pi type should produce InvalidCert mentioning Pi, got: {err}"
    );
}

// =========================================================================
// Let verification
// =========================================================================

#[test]
fn test_verify_let_basic() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    // let x : Type := Prop in x
    let type1 = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    let let_expr = Expr::let_named(
        Name::anon(),
        type1.clone(), // type annotation: Type
        prop.clone(),  // value: Prop
        Expr::from_kind(ExprKind::BVar(0)),
        false,
    );

    let cert = ProofCert::Let {
        type_cert: Box::new(ProofCert::Sort {
            level: Level::succ(Level::zero()),
        }),
        value_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        body_cert: Box::new(ProofCert::BVar {
            idx: 0,
            expected_type: Box::new(type1.clone()),
        }),
        result_type: Box::new(type1.clone()),
    };

    let ty = verifier
        .verify(&cert, &let_expr)
        .expect("let x : Type := Prop in x should verify");
    assert_eq!(ty, type1);
}

#[test]
fn test_verify_let_value_type_mismatch() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let nat_lit = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(42))));

    let let_expr = Expr::let_named(
        Name::anon(),
        prop.clone(),
        nat_lit.clone(),
        Expr::from_kind(ExprKind::BVar(0)),
        false,
    );

    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
    let cert = ProofCert::Let {
        type_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        value_cert: Box::new(ProofCert::Lit {
            lit: Literal::Nat(BigNat::Small(42)),
            type_: Box::new(nat_type),
        }),
        body_cert: Box::new(ProofCert::BVar {
            idx: 0,
            expected_type: Box::new(prop.clone()),
        }),
        result_type: Box::new(prop.clone()),
    };

    let err = verifier.verify(&cert, &let_expr).unwrap_err();
    assert!(
        matches!(err, CertError::TypeMismatch { ref location, .. } if location.contains("Let")),
        "Let with mismatched value type should produce TypeMismatch at Let, got: {err}"
    );
}

#[test]
fn test_verify_let_type_not_a_type() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    let nat_lit = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(42))));
    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    let let_expr = Expr::let_named(
        Name::anon(),
        nat_lit.clone(),
        nat_lit.clone(),
        Expr::from_kind(ExprKind::BVar(0)),
        false,
    );

    let cert = ProofCert::Let {
        type_cert: Box::new(ProofCert::Lit {
            lit: Literal::Nat(BigNat::Small(42)),
            type_: Box::new(nat_type.clone()),
        }),
        value_cert: Box::new(ProofCert::Lit {
            lit: Literal::Nat(BigNat::Small(42)),
            type_: Box::new(nat_type),
        }),
        body_cert: Box::new(ProofCert::BVar {
            idx: 0,
            expected_type: Box::new(prop),
        }),
        result_type: Box::new(Expr::from_kind(ExprKind::Sort(Level::zero()))),
    };

    let err = verifier.verify(&cert, &let_expr).unwrap_err();
    assert!(
        matches!(err, CertError::InvalidCert(ref msg) if msg.contains("Let")),
        "Let with non-type annotation should produce InvalidCert, got: {err}"
    );
}

// =========================================================================
// Const verification
// =========================================================================

#[test]
fn test_verify_const_basic() {
    let env = env_with_const();
    let mut verifier = CertVerifier::new(&env);

    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let expr = Expr::const_(Name::from_string("MyConst"), vec![]);

    let cert = ProofCert::Const {
        name: Name::from_string("MyConst"),
        levels: vec![],
        type_: Box::new(prop.clone()),
    };

    let ty = verifier
        .verify(&cert, &expr)
        .expect("Const MyConst should verify");
    assert_eq!(ty, prop);
}

#[test]
fn test_verify_const_polymorphic() {
    let env = env_with_poly_const();
    let mut verifier = CertVerifier::new(&env);

    let level = Level::succ(Level::zero());
    let expected_ty = Expr::from_kind(ExprKind::Sort(level.clone()));
    let expr = Expr::const_(Name::from_string("MyPoly"), vec![level.clone()]);

    let cert = ProofCert::Const {
        name: Name::from_string("MyPoly"),
        levels: vec![level],
        type_: Box::new(expected_ty.clone()),
    };

    let ty = verifier
        .verify(&cert, &expr)
        .expect("Const MyPoly.{1} should verify");
    assert_eq!(ty, expected_ty);
}

#[test]
fn test_verify_const_unknown() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    let expr = Expr::const_(Name::from_string("DoesNotExist"), vec![]);
    let cert = ProofCert::Const {
        name: Name::from_string("DoesNotExist"),
        levels: vec![],
        type_: Box::new(Expr::from_kind(ExprKind::Sort(Level::zero()))),
    };

    let err = verifier.verify(&cert, &expr).unwrap_err();
    assert!(
        matches!(err, CertError::UnknownConst(_)),
        "Const not in environment should produce UnknownConst, got: {err}"
    );
}

#[test]
fn test_verify_const_name_mismatch() {
    let env = env_with_const();
    let mut verifier = CertVerifier::new(&env);

    let expr = Expr::const_(Name::from_string("MyConst"), vec![]);
    let cert = ProofCert::Const {
        name: Name::from_string("Other"),
        levels: vec![],
        type_: Box::new(Expr::from_kind(ExprKind::Sort(Level::zero()))),
    };

    let err = verifier.verify(&cert, &expr).unwrap_err();
    assert!(
        matches!(err, CertError::StructureMismatch { .. }),
        "Const with name mismatch should produce StructureMismatch, got: {err}"
    );
}

#[test]
fn test_verify_const_level_mismatch() {
    let env = env_with_poly_const();
    let mut verifier = CertVerifier::new(&env);

    let expr = Expr::const_(Name::from_string("MyPoly"), vec![Level::zero()]);
    let cert = ProofCert::Const {
        name: Name::from_string("MyPoly"),
        levels: vec![Level::succ(Level::zero())],
        type_: Box::new(Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))),
    };

    let err = verifier.verify(&cert, &expr).unwrap_err();
    assert!(
        matches!(err, CertError::InvalidCert(_)),
        "Const with level mismatch should produce InvalidCert, got: {err}"
    );
}

#[test]
fn test_verify_const_type_forgery() {
    let env = env_with_const();
    let mut verifier = CertVerifier::new(&env);

    let expr = Expr::const_(Name::from_string("MyConst"), vec![]);
    let cert = ProofCert::Const {
        name: Name::from_string("MyConst"),
        levels: vec![],
        type_: Box::new(Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))),
    };

    let err = verifier.verify(&cert, &expr).unwrap_err();
    assert!(
        matches!(err, CertError::TypeMismatch { .. }),
        "Const with forged type should produce TypeMismatch, got: {err}"
    );
}

// =========================================================================
// Lit (String) verification
// =========================================================================

#[test]
fn test_verify_lit_string() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    let expr = Expr::str_lit("hello");
    let string_type = Expr::const_(Name::from_string("String"), vec![]);

    let cert = ProofCert::Lit {
        lit: Literal::String("hello".into()),
        type_: Box::new(string_type.clone()),
    };

    let ty = verifier
        .verify(&cert, &expr)
        .expect("Lit(String) cert should verify");
    assert_eq!(ty, string_type);
}

#[test]
fn test_verify_lit_value_mismatch() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    let expr = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(42))));

    let cert = ProofCert::Lit {
        lit: Literal::Nat(BigNat::Small(99)),
        type_: Box::new(Expr::const_(Name::from_string("Nat"), vec![])),
    };

    let err = verifier.verify(&cert, &expr).unwrap_err();
    assert!(
        matches!(err, CertError::StructureMismatch { .. }),
        "Lit with wrong value should produce StructureMismatch, got: {err}"
    );
}

#[test]
fn test_verify_lit_type_forgery() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    let expr = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(42))));
    let wrong_type = Expr::const_(Name::from_string("String"), vec![]);

    let cert = ProofCert::Lit {
        lit: Literal::Nat(BigNat::Small(42)),
        type_: Box::new(wrong_type),
    };

    let err = verifier.verify(&cert, &expr).unwrap_err();
    assert!(
        matches!(err, CertError::TypeMismatch { .. }),
        "Lit with forged type should produce TypeMismatch, got: {err}"
    );
}

// =========================================================================
// Pi error paths
// =========================================================================

#[test]
fn test_verify_pi_binder_mismatch() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let expr = Expr::pi(BinderInfo::Default, prop.clone(), prop.clone());

    let cert = ProofCert::Pi {
        binder_info: BinderInfo::Implicit,
        arg_type_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        arg_level: Level::succ(Level::zero()),
        body_type_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        body_level: Level::succ(Level::zero()),
    };

    let err = verifier.verify(&cert, &expr).unwrap_err();
    assert!(
        matches!(err, CertError::InvalidCert(ref msg) if msg.contains("Binder")),
        "Pi with binder info mismatch should produce InvalidCert, got: {err}"
    );
}

#[test]
fn test_verify_pi_level_mismatch() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let expr = Expr::pi(BinderInfo::Default, prop.clone(), prop.clone());

    let cert = ProofCert::Pi {
        binder_info: BinderInfo::Default,
        arg_type_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        arg_level: Level::zero(),
        body_type_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        body_level: Level::succ(Level::zero()),
    };

    let err = verifier.verify(&cert, &expr).unwrap_err();
    assert!(
        matches!(err, CertError::LevelMismatch { .. }),
        "Pi with wrong arg_level should produce LevelMismatch, got: {err}"
    );
}

// =========================================================================
// Lam error paths
// =========================================================================

#[test]
fn test_verify_lam_binder_mismatch() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let expr = Expr::lam(
        BinderInfo::Default,
        prop.clone(),
        Expr::from_kind(ExprKind::BVar(0)),
    );

    let cert = ProofCert::Lam {
        binder_info: BinderInfo::Implicit,
        arg_type_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        body_cert: Box::new(ProofCert::BVar {
            idx: 0,
            expected_type: Box::new(prop.clone()),
        }),
        result_type: Box::new(Expr::pi(BinderInfo::Default, prop.clone(), prop)),
    };

    let err = verifier.verify(&cert, &expr).unwrap_err();
    assert!(
        matches!(err, CertError::InvalidCert(ref msg) if msg.contains("Binder")),
        "Lam with binder info mismatch should produce InvalidCert, got: {err}"
    );
}

#[test]
fn test_verify_lam_arg_not_a_type() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    let nat_lit = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(42))));
    let expr = Expr::lam(
        BinderInfo::Default,
        nat_lit.clone(),
        Expr::from_kind(ExprKind::BVar(0)),
    );

    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
    let cert = ProofCert::Lam {
        binder_info: BinderInfo::Default,
        arg_type_cert: Box::new(ProofCert::Lit {
            lit: Literal::Nat(BigNat::Small(42)),
            type_: Box::new(nat_type),
        }),
        body_cert: Box::new(ProofCert::BVar {
            idx: 0,
            expected_type: Box::new(nat_lit.clone()),
        }),
        result_type: Box::new(Expr::from_kind(ExprKind::Sort(Level::zero()))),
    };

    let err = verifier.verify(&cert, &expr).unwrap_err();
    assert!(
        matches!(err, CertError::InvalidCert(ref msg) if msg.contains("not a type")),
        "Lam with non-Sort arg type should produce InvalidCert, got: {err}"
    );
}

// =========================================================================
// BVar / FVar / DefEq / mode / structure mismatch / register / K combinator
// =========================================================================

#[test]
fn test_verify_bvar_idx_mismatch() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);
    verifier
        .context
        .push(Expr::from_kind(ExprKind::Sort(Level::zero())));

    let expr = Expr::from_kind(ExprKind::BVar(0));
    let cert = ProofCert::BVar {
        idx: 1,
        expected_type: Box::new(Expr::from_kind(ExprKind::Sort(Level::zero()))),
    };

    let err = verifier.verify(&cert, &expr).unwrap_err();
    assert!(
        matches!(err, CertError::InvalidBVar(_)),
        "BVar with idx mismatch should produce InvalidBVar, got: {err}"
    );
}

#[test]
fn test_verify_bvar_expected_type_mismatch() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);
    verifier
        .context
        .push(Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))));

    let expr = Expr::from_kind(ExprKind::BVar(0));
    let cert = ProofCert::BVar {
        idx: 0,
        expected_type: Box::new(Expr::from_kind(ExprKind::Sort(Level::zero()))),
    };

    let err = verifier.verify(&cert, &expr).unwrap_err();
    assert!(
        matches!(err, CertError::TypeMismatch { ref location, .. } if location.contains("BVar")),
        "BVar with wrong expected_type should produce TypeMismatch, got: {err}"
    );
}

#[test]
fn test_verify_def_eq_valid() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    let expr = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let type1 = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));

    let cert = ProofCert::DefEq {
        inner: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        expected_type: Box::new(type1.clone()),
        actual_type: Box::new(type1.clone()),
        eq_steps: vec![DefEqStep::Refl],
    };

    let ty = verifier
        .verify(&cert, &expr)
        .expect("DefEq with matching types should verify");
    assert_eq!(ty, type1);
}

#[test]
fn test_verify_cubical_in_wrong_mode() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    let expr = Expr::from_kind(ExprKind::CubicalInterval);
    let cert = ProofCert::CubicalInterval;

    let err = verifier.verify(&cert, &expr).unwrap_err();
    assert!(
        matches!(err, CertError::ModeRequired { ref feature, .. } if feature == "CubicalInterval"),
        "CubicalInterval in Constructive mode should produce ModeRequired, got: {err}"
    );
}

#[test]
fn test_verify_sprop_in_wrong_mode() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    let expr = Expr::from_kind(ExprKind::SProp);
    let cert = ProofCert::SProp;

    let err = verifier.verify(&cert, &expr).unwrap_err();
    assert!(
        matches!(err, CertError::ModeRequired { ref feature, .. } if feature == "SProp"),
        "SProp in Constructive mode should produce ModeRequired, got: {err}"
    );
}

#[test]
fn test_verify_cubical_endpoint_wrong_mode() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    let expr = Expr::from_kind(ExprKind::CubicalI0);
    let cert = ProofCert::CubicalEndpoint { is_one: false };

    let err = verifier.verify(&cert, &expr).unwrap_err();
    assert!(
        matches!(err, CertError::ModeRequired { .. }),
        "CubicalEndpoint in Constructive mode should produce ModeRequired, got: {err}"
    );
}

#[test]
fn test_verify_sort_cert_on_bvar_expr() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    let expr = Expr::from_kind(ExprKind::BVar(0));
    let cert = ProofCert::Sort {
        level: Level::zero(),
    };

    let err = verifier.verify(&cert, &expr).unwrap_err();
    assert!(
        matches!(err, CertError::StructureMismatch { .. }),
        "Sort cert on BVar expr should produce StructureMismatch, got: {err}"
    );
}

#[test]
fn test_verify_fvar_cert_on_sort_expr() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    let expr = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let cert = ProofCert::FVar {
        id: FVarId(1),
        type_: Box::new(Expr::from_kind(ExprKind::Sort(Level::zero()))),
    };

    let err = verifier.verify(&cert, &expr).unwrap_err();
    assert!(
        matches!(err, CertError::StructureMismatch { .. }),
        "FVar cert on Sort expr should produce StructureMismatch, got: {err}"
    );
}

#[test]
fn test_verify_app_cert_on_sort_expr() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let cert = ProofCert::App {
        fn_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        fn_type: Box::new(prop.clone()),
        arg_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        result_type: Box::new(prop.clone()),
    };

    let err = verifier.verify(&cert, &prop).unwrap_err();
    assert!(
        matches!(err, CertError::StructureMismatch { .. }),
        "App cert on Sort expr should produce StructureMismatch, got: {err}"
    );
}

#[test]
fn test_register_fvar_same_type_ok() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    let fvar_id = FVarId(10);
    let ty = Expr::from_kind(ExprKind::Sort(Level::zero()));

    verifier.register_fvar(fvar_id, ty.clone()).unwrap();
    verifier.register_fvar(fvar_id, ty).unwrap();
}

#[test]
fn test_mode_set_and_get() {
    use crate::mode::CleanMode;

    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    assert_eq!(verifier.mode(), CleanMode::default());

    verifier.set_mode(CleanMode::Cubical);
    assert_eq!(verifier.mode(), CleanMode::Cubical);

    verifier.set_mode(CleanMode::Classical);
    assert_eq!(verifier.mode(), CleanMode::Classical);
}

#[test]
fn test_new_inherits_environment_mode() {
    use crate::mode::CleanMode;

    let env = Environment::with_mode(CleanMode::Cubical);
    let mut verifier = CertVerifier::new(&env);
    let expr = Expr::from_kind(ExprKind::CubicalInterval);
    let ty = verifier
        .verify(&ProofCert::CubicalInterval, &expr)
        .expect("CertVerifier::new should inherit cubical mode from the environment");

    assert_eq!(verifier.mode(), env.mode());
    assert_eq!(
        ty,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))
    );
}

#[test]
fn test_verify_sort_with_param_level() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    let u = Level::param(Name::from_string("u"));
    let expr = Expr::from_kind(ExprKind::Sort(u.clone()));
    let cert = ProofCert::Sort { level: u.clone() };

    let ty = verifier
        .verify(&cert, &expr)
        .expect("Sort(u) cert should verify");
    assert_eq!(ty, Expr::from_kind(ExprKind::Sort(Level::succ(u))));
}

#[test]
fn test_verify_pi_result_is_imax() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    let type0 = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let expr = Expr::pi(BinderInfo::Default, type0.clone(), type0.clone());

    let cert = ProofCert::Pi {
        binder_info: BinderInfo::Default,
        arg_type_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        arg_level: Level::succ(Level::zero()),
        body_type_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        body_level: Level::succ(Level::zero()),
    };

    let ty = verifier
        .verify(&cert, &expr)
        .expect("Pi (Prop → Prop) should verify");
    match &ty.kind {
        ExprKind::Sort(level) => {
            assert!(
                !level.is_zero(),
                "imax(succ(0), succ(0)) should not be zero"
            );
        }
        _ => panic!("Pi result should be Sort, got: {ty:?}"),
    }
}

fn bv(idx: u32) -> Expr {
    Expr::from_kind(ExprKind::BVar(idx))
}

fn k_combinator_expr() -> Expr {
    let type0 = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let lam_y = Expr::lam(BinderInfo::Default, bv(1), bv(1));
    let lam_x = Expr::lam(BinderInfo::Default, bv(0), lam_y);
    Expr::lam(BinderInfo::Default, type0, lam_x)
}

fn k_combinator_cert() -> ProofCert {
    let type0 = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let body_body_cert = ProofCert::BVar {
        idx: 1,
        expected_type: Box::new(bv(2)),
    };
    let body_cert = ProofCert::Lam {
        binder_info: BinderInfo::Default,
        arg_type_cert: Box::new(ProofCert::BVar {
            idx: 1,
            expected_type: Box::new(type0.clone()),
        }),
        body_cert: Box::new(body_body_cert),
        result_type: Box::new(Expr::pi(BinderInfo::Default, bv(1), bv(2))),
    };
    let lam_x_cert = ProofCert::Lam {
        binder_info: BinderInfo::Default,
        arg_type_cert: Box::new(ProofCert::BVar {
            idx: 0,
            expected_type: Box::new(type0.clone()),
        }),
        body_cert: Box::new(body_cert),
        result_type: Box::new(Expr::pi(
            BinderInfo::Default,
            bv(0),
            Expr::pi(BinderInfo::Default, bv(1), bv(2)),
        )),
    };
    ProofCert::Lam {
        binder_info: BinderInfo::Default,
        arg_type_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        body_cert: Box::new(lam_x_cert),
        result_type: Box::new(Expr::pi(
            BinderInfo::Default,
            type0,
            Expr::pi(
                BinderInfo::Default,
                bv(0),
                Expr::pi(BinderInfo::Default, bv(1), bv(2)),
            ),
        )),
    }
}

#[test]
fn test_verify_nested_lam_const_combinator() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);
    let result = verifier.verify(&k_combinator_cert(), &k_combinator_expr());
    assert!(
        result.is_ok(),
        "K combinator cert should verify, got: {:?}",
        result.err()
    );
}

#[test]
fn rejected_scoped_certificate_does_not_leak_binder_authority() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);
    let prop = Expr::prop();
    let lam = Expr::lam(BinderInfo::Default, prop.clone(), bv(0));
    let malformed = ProofCert::Lam {
        binder_info: BinderInfo::Default,
        arg_type_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        // The expression body is BVar(0), so this certificate fails only
        // after the Lam verifier has extended its local context.
        body_cert: Box::new(ProofCert::BVar {
            idx: 1,
            expected_type: Box::new(prop.clone()),
        }),
        result_type: Box::new(Expr::pi(BinderInfo::Default, prop.clone(), prop.clone())),
    };
    assert!(verifier.verify(&malformed, &lam).is_err());

    let free_bvar = bv(0);
    let forged = ProofCert::BVar {
        idx: 0,
        expected_type: Box::new(prop),
    };
    assert!(
        matches!(
            verifier.verify(&forged, &free_bvar),
            Err(CertError::InvalidBVar(0))
        ),
        "a rejected scoped proof must not leave a reusable verifier context"
    );
}
