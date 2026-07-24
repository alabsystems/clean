// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

#![cfg(feature = "geometry-tools")]

//! Tests for to_micro_cert coverage (#1284).
//!
//! The `GeometryCertGenerator::to_micro_cert` function converts `(ProofCert, Expr)`
//! pairs into `(MicroCert, MicroExpr)` for independent verification by the
//! MicroChecker. It has 6 match arms but only the Const arm had direct tests.
//! These tests cover the remaining 5 arms plus a negative test for mismatched
//! Lit values and an unsupported-arm test.

use clean_kernel::cert::geometry::GeometryCertGenerator;
use clean_kernel::cert::ProofCert;
use clean_kernel::expr::ExprKind;
use clean_kernel::{Environment, Expr, FVarId, Level, Literal, Name};
use std::sync::Arc;

/// Helper: create an initialized GeometryCertGenerator.
fn make_gen() -> GeometryCertGenerator {
    let mut env = Environment::with_prelude();
    env.init_computational_geometry()
        .expect("computational geometry init should succeed");
    GeometryCertGenerator::new(env).unwrap()
}

// ============================================================================
// Sort arm
// ============================================================================

#[test]
fn to_micro_cert_sort_zero() {
    let generator = make_gen();
    let level = Level::zero();
    let cert = ProofCert::Sort {
        level: level.clone(),
    };
    let expr = Expr::sort(level);

    let (micro_cert, micro_expr) = generator
        .to_micro_cert(&cert, &expr)
        .expect("to_micro_cert should succeed for Sort(0)");
    assert!(
        matches!(micro_cert, clean_kernel::micro::MicroCert::Sort { .. }),
        "Sort cert should convert to MicroCert::Sort, got: {:?}",
        micro_cert
    );
    assert!(
        matches!(micro_expr, clean_kernel::micro::MicroExpr::Sort(_)),
        "Sort expr should convert to MicroExpr::Sort, got: {:?}",
        micro_expr
    );
}

#[test]
fn to_micro_cert_sort_nonzero() {
    let generator = make_gen();
    let level = Level::succ(Level::succ(Level::zero())); // Sort 2
    let cert = ProofCert::Sort {
        level: level.clone(),
    };
    let expr = Expr::sort(level);

    let (micro_cert, micro_expr) = generator
        .to_micro_cert(&cert, &expr)
        .expect("to_micro_cert should succeed for Sort(2)");
    assert!(matches!(
        micro_cert,
        clean_kernel::micro::MicroCert::Sort { .. }
    ));
    assert!(matches!(
        micro_expr,
        clean_kernel::micro::MicroExpr::Sort(_)
    ));
}

// ============================================================================
// FVar arm
// ============================================================================

#[test]
fn to_micro_cert_fvar() {
    let generator = make_gen();
    // FVar type must be convertible by MicroExpr::from_kernel — use Sort (Prop).
    let fvar_type = Expr::sort(Level::zero());
    let cert = ProofCert::FVar {
        id: FVarId::new(42),
        type_: Box::new(fvar_type),
    };
    let expr = Expr::fvar(FVarId::new(42));

    let (micro_cert, micro_expr) = generator
        .to_micro_cert(&cert, &expr)
        .expect("to_micro_cert should succeed for FVar");
    assert!(
        matches!(micro_cert, clean_kernel::micro::MicroCert::Opaque { .. }),
        "FVar cert should convert to MicroCert::Opaque, got: {:?}",
        micro_cert
    );
    assert!(
        matches!(micro_expr, clean_kernel::micro::MicroExpr::Opaque(_)),
        "FVar expr should convert to MicroExpr::Opaque, got: {:?}",
        micro_expr
    );
}

// ============================================================================
// Lit arm
// ============================================================================

#[test]
fn to_micro_cert_lit_nat() {
    let generator = make_gen();
    let lit_val = Literal::nat(7);
    let lit_type = Expr::sort(Level::zero()); // must be from_kernel-convertible
    let cert = ProofCert::Lit {
        lit: lit_val,
        type_: Box::new(lit_type),
    };
    let expr = Expr::nat_lit(7);

    let (micro_cert, micro_expr) = generator
        .to_micro_cert(&cert, &expr)
        .expect("to_micro_cert should succeed for Lit(Nat)");
    let nat7 = clean_kernel::micro::MicroLiteral::nat_u64(7);
    assert!(
        matches!(
            &micro_cert,
            clean_kernel::micro::MicroCert::Lit { lit, .. } if *lit == nat7
        ),
        "Lit cert should convert to MicroCert::Lit with Nat(7), got: {:?}",
        micro_cert
    );
    assert!(
        matches!(
            &micro_expr,
            clean_kernel::micro::MicroExpr::Lit(l) if *l == nat7
        ),
        "Lit expr should convert to MicroExpr::Lit(Nat(7)), got: {:?}",
        micro_expr
    );
}

#[test]
fn to_micro_cert_lit_string() {
    let generator = make_gen();
    let lit_val = Literal::String(Arc::from("hello"));
    let lit_type = Expr::sort(Level::zero());
    let cert = ProofCert::Lit {
        lit: lit_val,
        type_: Box::new(lit_type),
    };
    let expr = Expr::str_lit("hello");

    let (micro_cert, micro_expr) = generator
        .to_micro_cert(&cert, &expr)
        .expect("to_micro_cert should succeed for Lit(String)");
    assert!(
        matches!(micro_cert, clean_kernel::micro::MicroCert::Lit { .. }),
        "String Lit cert should convert to MicroCert::Lit, got: {:?}",
        micro_cert
    );
    assert!(
        matches!(micro_expr, clean_kernel::micro::MicroExpr::Lit(_)),
        "String Lit expr should convert to MicroExpr::Lit, got: {:?}",
        micro_expr
    );
}

// ============================================================================
// App arm
// ============================================================================

#[test]
fn to_micro_cert_app() {
    let generator = make_gen();

    // Build App(f, a) where both f and a are Consts with from_kernel-convertible types.
    // Use Expr::sort(Level::zero()) as the type_ since MicroExpr::from_kernel handles Sort.
    let fn_name = Name::from_string("test_fn");
    let arg_name = Name::from_string("test_arg");
    let fn_levels = vec![Level::zero()];
    let arg_levels = vec![Level::zero()];

    let fn_cert = ProofCert::Const {
        name: fn_name.clone(),
        levels: fn_levels.clone(),
        type_: Box::new(Expr::sort(Level::zero())),
    };
    let arg_cert = ProofCert::Const {
        name: arg_name.clone(),
        levels: arg_levels.clone(),
        type_: Box::new(Expr::sort(Level::zero())),
    };

    // Result type must be from_kernel-convertible — use Prop.
    let cert = ProofCert::App {
        fn_cert: Box::new(fn_cert),
        fn_type: Box::new(Expr::sort(Level::zero())),
        arg_cert: Box::new(arg_cert),
        result_type: Box::new(Expr::sort(Level::zero())),
    };
    let expr = Expr::app(
        Expr::const_(fn_name, fn_levels),
        Expr::const_(arg_name, arg_levels),
    );

    let (micro_cert, micro_expr) = generator
        .to_micro_cert(&cert, &expr)
        .expect("to_micro_cert should succeed for App");
    assert!(
        matches!(micro_cert, clean_kernel::micro::MicroCert::App { .. }),
        "App cert should convert to MicroCert::App, got: {:?}",
        micro_cert
    );
    assert!(
        matches!(micro_expr, clean_kernel::micro::MicroExpr::App(_, _)),
        "App expr should convert to MicroExpr::App, got: {:?}",
        micro_expr
    );
}

// ============================================================================
// Proj arm
// ============================================================================

#[test]
fn to_micro_cert_proj() {
    let generator = make_gen();

    // Inner expression is a Const with from_kernel-convertible type.
    let inner_name = Name::from_string("test_struct_val");
    let inner_levels = vec![Level::zero()];
    let inner_type = Expr::sort(Level::zero());

    let inner_cert = ProofCert::Const {
        name: inner_name.clone(),
        levels: inner_levels.clone(),
        type_: Box::new(inner_type.clone()),
    };

    let struct_name = Name::from_string("TestStruct");
    let field_type = Expr::sort(Level::zero()); // must be from_kernel-convertible
    let cert = ProofCert::Proj {
        struct_name: struct_name.clone(),
        idx: 0,
        expr_cert: Box::new(inner_cert),
        expr_type: Box::new(inner_type),
        field_type: Box::new(field_type),
    };
    let expr = Expr::proj(struct_name, 0, Expr::const_(inner_name, inner_levels));

    let (micro_cert, micro_expr) = generator
        .to_micro_cert(&cert, &expr)
        .expect("to_micro_cert should succeed for Proj");
    assert!(
        matches!(
            micro_cert,
            clean_kernel::micro::MicroCert::Proj { idx: 0, .. }
        ),
        "Proj cert should convert to MicroCert::Proj with idx=0, got: {:?}",
        micro_cert
    );
    assert!(
        matches!(micro_expr, clean_kernel::micro::MicroExpr::Proj(0, _)),
        "Proj expr should convert to MicroExpr::Proj(0, _), got: {:?}",
        micro_expr
    );
}

// ============================================================================
// Negative tests
// ============================================================================

#[test]
fn to_micro_cert_lit_mismatch_independently_sourced() {
    // Negative test: cert Lit and expr Lit are independently sourced.
    // to_micro_cert should succeed even with mismatched values — the
    // micro-checker is responsible for catching the mismatch, not
    // to_micro_cert itself.
    let generator = make_gen();

    let cert = ProofCert::Lit {
        lit: Literal::nat(42),
        type_: Box::new(Expr::sort(Level::zero())),
    };
    // Expression has a DIFFERENT literal value.
    let expr = Expr::nat_lit(99);

    let result = generator.to_micro_cert(&cert, &expr);
    assert!(
        result.is_some(),
        "to_micro_cert should succeed even with mismatched Lit values — \
         the micro-checker catches mismatches, not the conversion"
    );

    let (micro_cert, micro_expr) = result.unwrap();
    // Verify the cert and expr literals are independently sourced.
    let cert_nat = match &micro_cert {
        clean_kernel::micro::MicroCert::Lit {
            lit: clean_kernel::micro::MicroLiteral::Nat(n),
            ..
        } => n.clone(),
        other => panic!("expected MicroCert::Lit(Nat), got: {:?}", other),
    };
    let expr_nat = match &micro_expr {
        clean_kernel::micro::MicroExpr::Lit(clean_kernel::micro::MicroLiteral::Nat(n)) => n.clone(),
        other => panic!("expected MicroExpr::Lit(Nat), got: {:?}", other),
    };

    assert_eq!(cert_nat.to_string(), "42", "cert literal should be 42");
    assert_eq!(expr_nat.to_string(), "99", "expr literal should be 99");
    assert_ne!(
        cert_nat, expr_nat,
        "cert and expr literals must be independently sourced (different values)"
    );
}

#[test]
fn to_micro_cert_returns_none_for_unsupported() {
    // Unsupported combinations should return None.
    let generator = make_gen();

    // BVar cert with BVar expr — not handled by to_micro_cert.
    let cert = ProofCert::BVar {
        idx: 0,
        expected_type: Box::new(Expr::sort(Level::zero())),
    };
    let expr = Expr::from_kind(ExprKind::BVar(0));

    let result = generator.to_micro_cert(&cert, &expr);
    assert!(
        result.is_none(),
        "BVar should not be handled by to_micro_cert"
    );
}
