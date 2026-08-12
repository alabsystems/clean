// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_create_cert_verifier_empty_context() {
    let env = Environment::new();
    let ctx = ElabCtx::new(&env);

    let mut verifier = ctx
        .create_cert_verifier()
        .expect("create_cert_verifier should succeed on empty elaboration context");
    let verified_type = verifier
        .verify(
            &ProofCert::Sort {
                level: Level::zero(),
            },
            &Expr::sort(Level::zero()),
        )
        .expect("verifier from empty context should check closed Sort certificates");
    assert_eq!(verified_type, Expr::sort(Level::succ(Level::zero())));
}

#[test]
fn test_infer_type_with_cert_sort() {
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    let surface = parse_expr("Type").unwrap();
    let expr = ctx.elaborate(&surface).unwrap();

    let (ty, cert) = ctx
        .infer_type_with_cert(&expr)
        .expect("infer_type_with_cert for Sort should succeed");
    assert!(matches!(ty.kind(), ExprKind::Sort(_)));
    assert!(matches!(cert, ProofCert::Sort { .. }));
}

#[test]
fn test_infer_type_with_cert_lambda() {
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    let surface = parse_expr("fun (x : Type) => x").unwrap();
    let expr = ctx.elaborate(&surface).unwrap();

    let (ty, cert) = ctx
        .infer_type_with_cert(&expr)
        .expect("infer_type_with_cert for lambda should succeed");
    assert!(matches!(ty.kind(), ExprKind::Pi(_, _, _)));
    assert!(matches!(cert, ProofCert::Lam { .. }));
}

#[test]
fn test_elaborate_and_verify_type() {
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    let surface = parse_expr("Type").unwrap();
    let (expr, ty, cert) = ctx
        .elaborate_and_verify(&surface)
        .expect("elaborate_and_verify Type should succeed");
    assert!(matches!(expr.kind(), ExprKind::Sort(_)));
    assert!(matches!(ty.kind(), ExprKind::Sort(_)));
    assert!(matches!(cert, ProofCert::Sort { .. }));
}

#[test]
fn test_elaborate_and_verify_lambda() {
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    let surface = parse_expr("fun (A : Type) (x : A) => x").unwrap();
    let (expr, ty, cert) = ctx
        .elaborate_and_verify(&surface)
        .expect("elaborate_and_verify lambda should succeed");
    assert!(matches!(expr.kind(), ExprKind::Lam(_, _, _)));
    assert!(matches!(ty.kind(), ExprKind::Pi(_, _, _)));
    assert!(matches!(cert, ProofCert::Lam { .. }));
}

#[test]
fn test_elaborate_and_verify_nat_lit() {
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    let surface = parse_expr("42").unwrap();
    let (expr, _ty, cert) = ctx
        .elaborate_and_verify(&surface)
        .expect("elaborate_and_verify nat literal should succeed");
    assert!(matches!(expr.kind(), ExprKind::Lit(Literal::Nat(n)) if n.to_u64() == Some(42)));
    assert!(matches!(cert, ProofCert::Lit { .. }));
}

#[test]
fn test_cert_verifier_with_local_context() {
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    let surface = parse_expr("fun (x : Type) => x").unwrap();
    let expr = ctx.elaborate(&surface).unwrap();
    let (ty, cert) = ctx.infer_type_with_cert(&expr).unwrap();

    let mut verifier = ctx.create_cert_verifier().unwrap();
    let verified_ty = verifier
        .verify(&cert, &expr)
        .expect("verifier with local context should validate inferred certificate");
    assert_eq!(verified_ty, ty);
}

#[test]
fn test_elaborate_and_verify_pi() {
    let env = Environment::new();
    let mut ctx = ElabCtx::new(&env);

    let surface = parse_expr("forall (x : Type), x").unwrap();
    let (expr, ty, cert) = ctx
        .elaborate_and_verify(&surface)
        .expect("elaborate_and_verify Pi should succeed");
    assert!(matches!(expr.kind(), ExprKind::Pi(_, _, _)));
    assert!(matches!(ty.kind(), ExprKind::Sort(_)));
    assert!(matches!(cert, ProofCert::Pi { .. }));
}

#[test]
fn test_create_cert_verifier_uses_environment_mode_for_cubical_interval() {
    let env = Environment::with_mode(clean_kernel::mode::CleanMode::Cubical);
    let ctx = ElabCtx::new(&env);
    let interval = Expr::from_kind(ExprKind::CubicalInterval);

    let mut verifier = ctx
        .create_cert_verifier()
        .expect("create_cert_verifier should preserve cubical mode");
    let verified_ty = verifier
        .verify(&ProofCert::CubicalInterval, &interval)
        .expect("verifier should accept cubical interval in cubical mode");

    assert_eq!(verified_ty, Expr::sort(Level::succ(Level::zero())));
}

#[test]
fn test_infer_type_with_cert_uses_environment_mode_for_cubical_interval() {
    let env = Environment::with_mode(clean_kernel::mode::CleanMode::Cubical);
    let ctx = ElabCtx::new(&env);
    let interval = Expr::from_kind(ExprKind::CubicalInterval);

    let (ty, cert) = ctx
        .infer_type_with_cert(&interval)
        .expect("infer_type_with_cert should preserve cubical mode");

    assert_eq!(ty, Expr::sort(Level::succ(Level::zero())));
    assert!(matches!(cert, ProofCert::CubicalInterval));
}
