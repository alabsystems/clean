// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use crate::expr::{Expr, ExprKind};
use crate::level::Level;

use super::*;

fn l0() -> MicroLevel {
    MicroLevel::Zero
}
fn l1() -> MicroLevel {
    MicroLevel::succ(l0())
}
fn sort(l: MicroLevel) -> MicroExpr {
    MicroExpr::Sort(l)
}
fn bvar(i: u32) -> MicroExpr {
    MicroExpr::BVar(i)
}
fn app(f: MicroExpr, a: MicroExpr) -> MicroExpr {
    MicroExpr::App(Arc::new(f), Arc::new(a))
}
fn lam(ty: MicroExpr, body: MicroExpr) -> MicroExpr {
    MicroExpr::Lam(Arc::new(ty), Arc::new(body))
}
fn pi(ty: MicroExpr, body: MicroExpr) -> MicroExpr {
    MicroExpr::Pi(Arc::new(ty), Arc::new(body))
}
fn let_(ty: MicroExpr, val: MicroExpr, body: MicroExpr) -> MicroExpr {
    MicroExpr::Let(Arc::new(ty), Arc::new(val), Arc::new(body))
}
fn lit_nat(n: u64) -> MicroExpr {
    MicroExpr::Lit(MicroLiteral::nat_u64(n))
}
fn lit_str(s: &str) -> MicroExpr {
    MicroExpr::Lit(MicroLiteral::String(Arc::from(s)))
}
fn proj(idx: u32, e: MicroExpr) -> MicroExpr {
    MicroExpr::Proj(idx, Arc::new(e))
}

// ========================================================================
// Expression operations tests
// ========================================================================

#[test]
fn test_lift_bvar() {
    let e = bvar(0);
    assert_eq!(e.lift(0, 1), bvar(1));
    assert_eq!(e.lift(1, 1), bvar(0)); // Below cutoff, unchanged
}

#[test]
fn test_lift_lambda() {
    // λ x. x  (body is BVar(0))
    let e = lam(sort(l0()), bvar(0));
    // Lifting doesn't affect bound variables inside binders
    let lifted = e.lift(0, 1);
    assert_eq!(lifted, lam(sort(l0()), bvar(0)));
}

#[test]
fn test_instantiate_simple() {
    // BVar(0)[val/0] = val
    let e = bvar(0);
    let val = sort(l0());
    assert_eq!(e.instantiate(&val), val);
}

#[test]
fn test_instantiate_higher_index() {
    // BVar(1)[val/0] = BVar(0) (index decreases)
    let e = bvar(1);
    let val = sort(l0());
    assert_eq!(e.instantiate(&val), bvar(0));
}

#[test]
fn test_instantiate_under_binder() {
    // (λ x. BVar(1))[val/0] = λ x. val
    // The BVar(1) refers to the outer variable (index 0 at depth 0)
    let e = lam(sort(l0()), bvar(1));
    let val = sort(l1());
    let result = e.instantiate(&val);
    // After substitution: λ x. Sort(1)
    assert_eq!(result, lam(sort(l0()), sort(l1())));
}

// ========================================================================
// Level tests
// ========================================================================

#[test]
fn test_level_eq() {
    assert!(l0().level_eq(&l0()));
    assert!(l1().level_eq(&l1()));
    assert!(!l0().level_eq(&l1()));
}

#[test]
fn test_imax_zero_right() {
    // imax(l, 0) = 0
    let l = MicroLevel::imax(l1(), l0());
    assert_eq!(l, l0());
}

// ========================================================================
// WHNF tests
// ========================================================================

#[test]
fn test_whnf_sort() {
    let checker = MicroChecker::new();
    let e = sort(l0());
    assert_eq!(checker.whnf(&e), e);
}

#[test]
fn test_whnf_beta() {
    // (λ x. x) y → y
    let checker = MicroChecker::new();
    let id = lam(sort(l0()), bvar(0));
    let e = app(id, sort(l1()));
    assert_eq!(checker.whnf(&e), sort(l1()));
}

#[test]
fn test_whnf_nested_beta() {
    // (λ x. λ y. x) a b → a
    let checker = MicroChecker::new();
    let f = lam(sort(l0()), lam(sort(l0()), bvar(1)));
    let e = app(app(f, sort(l1())), sort(l0()));
    assert_eq!(checker.whnf(&e), sort(l1()));
}

#[test]
fn test_whnf_zeta() {
    // let x := v in x → v
    let checker = MicroChecker::new();
    let e = let_(sort(l0()), sort(l1()), bvar(0));
    assert_eq!(checker.whnf(&e), sort(l1()));
}

// ========================================================================
// Verification tests
// ========================================================================

#[test]
fn test_verify_sort() {
    let mut checker = MicroChecker::new();
    let expr = sort(l0());
    let cert = MicroCert::Sort { level: l0() };

    let ty = checker
        .verify(&cert, &expr)
        .expect("Sort(0) should verify successfully");
    assert_eq!(ty, sort(l1()));
}

#[test]
fn test_verify_sort_level_mismatch() {
    let mut checker = MicroChecker::new();
    let expr = sort(l0());
    let cert = MicroCert::Sort { level: l1() };

    let result = checker.verify(&cert, &expr);
    assert!(matches!(result, Err(MicroError::LevelMismatch { .. })));
}

#[test]
fn test_verify_pi() {
    // Prop → Prop : Type 0
    let mut checker = MicroChecker::new();
    let prop = sort(l0());
    let expr = pi(prop.clone(), prop.clone());

    let cert = MicroCert::Pi {
        arg_ty_cert: Box::new(MicroCert::Sort { level: l0() }),
        arg_level: l1(),
        body_ty_cert: Box::new(MicroCert::Sort { level: l0() }),
        body_level: l1(),
    };

    let ty = checker
        .verify(&cert, &expr)
        .expect("Pi(Prop, Prop) should verify successfully");
    // imax(1, 1) = 1
    assert_eq!(ty, sort(MicroLevel::imax(l1(), l1())));
}

#[test]
fn test_verify_identity() {
    // λ (x : Prop). x : Prop → Prop
    let mut checker = MicroChecker::new();
    let prop = sort(l0());
    let expr = lam(prop.clone(), bvar(0));

    let expected_ty = pi(prop.clone(), prop.clone());

    let cert = MicroCert::Lam {
        arg_ty_cert: Box::new(MicroCert::Sort { level: l0() }),
        body_cert: Box::new(MicroCert::BVar {
            idx: 0,
            ty: Box::new(prop.clone()),
        }),
        result_ty: Box::new(expected_ty.clone()),
    };

    let ty = checker
        .verify(&cert, &expr)
        .expect("Identity lambda should verify successfully");
    assert_eq!(ty, expected_ty);
}

#[test]
fn test_verify_bvar_forged_type_rejected() {
    // Forged certificate: claims BVar(0) has type Type 1 but the binder
    // declares the parameter as Prop (Sort(0)). The micro-checker must
    // cross-check the certificate type against the context and reject.
    let mut checker = MicroChecker::new();
    let prop = sort(l0());
    let type1 = sort(l1()); // Wrong type — binder says Prop

    // λ (x : Prop). x  — but certificate claims x : Type 1
    let expr = lam(prop.clone(), bvar(0));

    let cert = MicroCert::Lam {
        arg_ty_cert: Box::new(MicroCert::Sort { level: l0() }),
        body_cert: Box::new(MicroCert::BVar {
            idx: 0,
            ty: Box::new(type1), // Forged: should be Prop
        }),
        result_ty: Box::new(pi(prop.clone(), prop.clone())),
    };

    let result = checker.verify(&cert, &expr);
    assert!(
        matches!(result, Err(MicroError::TypeMismatch { .. })),
        "Forged BVar type should be rejected, got: {result:?}"
    );
}

#[test]
fn test_verify_app() {
    // (λ (A : Type). A) Prop : Type
    //
    // Note: λ (A : Type). A returns its argument, which is a Type.
    // The body `A` (BVar(0)) has type `Type` (from the binder).
    // So the lambda has type `Type → Type`, not `(A : Type) → A`.
    //
    // When applied to Prop, the result is Prop, which has type Type.

    let mut checker = MicroChecker::new();
    let type0 = sort(l0()); // Type 0 = Prop
    let type1 = sort(l1()); // Type 1

    // Identity on types: λ (A : Type). A
    // Expression: Lam(Sort(l1), BVar(0))
    let id_type = lam(type1.clone(), bvar(0));

    // Type of id: Type → Type
    // The body (BVar(0)) has type Type (from the binder), so result type is Type
    let id_ty = pi(type1.clone(), type1.clone());

    // Verify the lambda alone
    let lam_cert = MicroCert::Lam {
        arg_ty_cert: Box::new(MicroCert::Sort { level: l1() }),
        body_cert: Box::new(MicroCert::BVar {
            idx: 0,
            ty: Box::new(type1.clone()),
        }),
        result_ty: Box::new(id_ty.clone()),
    };
    let lam_ty = checker
        .verify(&lam_cert, &id_type)
        .expect("Lambda (Type → Type) should verify");
    assert_eq!(lam_ty, id_ty, "Lambda type should be Type → Type");

    // Verify the argument alone (Prop : Type)
    let arg_cert = MicroCert::Sort { level: l0() };
    let arg_ty = checker
        .verify(&arg_cert, &type0)
        .expect("Sort(0) argument should verify");
    assert_eq!(arg_ty, type1.clone(), "Prop should have type Type");

    // The app: (λ (A : Type). A) Prop
    let expr = app(id_type.clone(), type0.clone());

    // Result type: Type (from the Pi body which is Type, no substitution needed)
    let cert = MicroCert::App {
        fn_cert: Box::new(lam_cert.clone()),
        arg_cert: Box::new(arg_cert),
        result_ty: Box::new(type1.clone()), // The result type is Type
    };

    let ty = checker
        .verify(&cert, &expr)
        .expect("App((λ A:Type. A) Prop) should verify");
    assert_eq!(ty, type1);
}

#[test]
fn test_verify_let() {
    // let x : Type 1 := Type 0 in x : Type 1
    // The body type is Type 1, after substituting value it's still Type 1
    // (not the value itself - the TYPE of the body after substitution)
    let mut checker = MicroChecker::new();
    let type1 = sort(l1()); // Type 1
    let type0 = sort(l0()); // Type 0 = Prop

    // let x : Type 1 := Type 0 in x
    let expr = let_(type1.clone(), type0.clone(), bvar(0));

    let cert = MicroCert::Let {
        // Type 1 : Type 2
        ty_cert: Box::new(MicroCert::Sort { level: l1() }),
        // Type 0 : Type 1 (but we need Type 0 to have Type 1, which it does!)
        val_cert: Box::new(MicroCert::Sort { level: l0() }),
        // In body context, x : Type 1, so x has type Type 1
        body_cert: Box::new(MicroCert::BVar {
            idx: 0,
            ty: Box::new(type1.clone()),
        }),
        // After substitution: Type 1[Type 0/x] = Type 1
        // The body_ty is Type 1, instantiating doesn't change it
        result_ty: Box::new(type1.clone()),
    };

    let ty = checker
        .verify(&cert, &expr)
        .expect("Let expression should verify");
    assert_eq!(ty, type1);
}

#[test]
fn test_verify_structure_mismatch() {
    let mut checker = MicroChecker::new();
    let expr = sort(l0());
    let cert = MicroCert::BVar {
        idx: 0,
        ty: Box::new(sort(l0())),
    };

    let result = checker.verify(&cert, &expr);
    assert!(matches!(result, Err(MicroError::StructureMismatch)));
}

#[test]
fn test_verify_nested_lambda() {
    // λ (A : Type). λ (x : A). x : (A : Type) → A → A
    let mut checker = MicroChecker::new();
    let type0 = sort(l0());

    // Inner: λ (x : A). x where A is BVar(0) from outer
    let inner = lam(bvar(0), bvar(0));
    // Outer: λ (A : Type). inner
    let expr = lam(type0.clone(), inner);

    // Inner type: A → A (where A is BVar(0))
    let inner_ty = pi(bvar(0), bvar(1));
    // Outer type: (A : Type) → A → A
    let outer_ty = pi(type0.clone(), inner_ty.clone());

    let cert = MicroCert::Lam {
        arg_ty_cert: Box::new(MicroCert::Sort { level: l0() }),
        body_cert: Box::new(MicroCert::Lam {
            arg_ty_cert: Box::new(MicroCert::BVar {
                idx: 0,
                ty: Box::new(type0.clone()),
            }),
            body_cert: Box::new(MicroCert::BVar {
                idx: 0,
                ty: Box::new(bvar(1)), // x : A (shifted by 1)
            }),
            result_ty: Box::new(inner_ty.clone()),
        }),
        result_ty: Box::new(outer_ty.clone()),
    };

    let ty = checker
        .verify(&cert, &expr)
        .expect("Nested lambda should verify");
    assert_eq!(ty, outer_ty);
}

#[test]
fn test_verify_type_mismatch_in_app() {
    // Try to apply identity (Prop → Prop) to Type (wrong argument type)
    let mut checker = MicroChecker::new();
    let prop = sort(l0());
    let type1 = sort(l1());
    let id = lam(prop.clone(), bvar(0));
    let expr = app(id.clone(), type1.clone());

    let id_ty = pi(prop.clone(), prop.clone());

    let cert = MicroCert::App {
        fn_cert: Box::new(MicroCert::Lam {
            arg_ty_cert: Box::new(MicroCert::Sort { level: l0() }),
            body_cert: Box::new(MicroCert::BVar {
                idx: 0,
                ty: Box::new(prop.clone()),
            }),
            result_ty: Box::new(id_ty),
        }),
        // Wrong! Argument is Type 1, but function expects Prop
        arg_cert: Box::new(MicroCert::Sort { level: l1() }),
        result_ty: Box::new(type1),
    };

    let result = checker.verify(&cert, &expr);
    assert!(matches!(result, Err(MicroError::TypeMismatch { .. })));
}

// ========================================================================
// Contract tests
// ========================================================================

#[test]
fn test_contract_micro_level_succ() {
    let zero = MicroLevel::Zero;
    let succ_zero = MicroLevel::succ(zero.clone());
    assert_eq!(succ_zero, MicroLevel::Succ(Arc::new(zero)));
}

#[test]
fn test_contract_micro_level_max_idempotent() {
    let zero = MicroLevel::Zero;
    let one = MicroLevel::succ(MicroLevel::Zero);
    let max_01 = MicroLevel::Max(Arc::new(MicroLevel::Zero), Arc::new(one.clone()));

    let levels = [zero, one, max_01];
    for level in levels {
        let max_ll = MicroLevel::max(level.clone(), level.clone());
        assert_eq!(
            max_ll, level,
            "max(l, l) should simplify to l for {level:?}"
        );
    }
}

#[test]
fn test_contract_micro_level_imax_succ_second_arg() {
    let l1 = MicroLevel::succ(MicroLevel::Zero);
    let l2 = MicroLevel::succ(MicroLevel::succ(MicroLevel::Zero));
    let imax = MicroLevel::imax(l1.clone(), l2.clone());
    let expected = MicroLevel::max(l1, l2);
    assert_eq!(imax, expected, "imax(_, succ(_)) should reduce to max");
}

#[test]
fn test_contract_verify_restores_context() {
    let mut checker = MicroChecker::new();
    let prop = sort(l0());
    let expr = lam(prop.clone(), bvar(0));
    let expected_ty = pi(prop.clone(), prop.clone());

    let cert = MicroCert::Lam {
        arg_ty_cert: Box::new(MicroCert::Sort { level: l0() }),
        body_cert: Box::new(MicroCert::BVar {
            idx: 0,
            ty: Box::new(prop.clone()),
        }),
        result_ty: Box::new(expected_ty),
    };

    let ty = checker
        .verify(&cert, &expr)
        .expect("Lambda should verify before context check");
    assert_eq!(ty, pi(prop.clone(), prop.clone()));

    // Context should be empty after verification.
    let bvar_cert = MicroCert::BVar {
        idx: 0,
        ty: Box::new(prop),
    };
    let result = checker.verify(&bvar_cert, &bvar(0));
    assert!(matches!(result, Err(MicroError::InvalidBVar(_))));
}

#[test]
fn test_def_eq_beta() {
    // (λ x. x) y ≡ y
    let checker = MicroChecker::new();
    let id = lam(sort(l0()), bvar(0));
    let y = sort(l1());
    let app_e = app(id, y.clone());

    assert!(checker.def_eq(&app_e, &y));
}

#[test]
fn test_def_eq_under_binder() {
    // WHNF doesn't reduce under binders, so λ x. (λ y. y) x ≢ λ x. x
    // This is intentional - micro-checker only does WHNF at the head
    // For full definitional equality under binders, you'd need eta/deep reduction
    //
    // Instead, test that def_eq works for structurally equal lambdas
    let checker = MicroChecker::new();
    let lhs = lam(sort(l0()), bvar(0));
    let rhs = lam(sort(l0()), bvar(0));

    assert!(checker.def_eq(&lhs, &rhs));

    // And different lambdas are not equal
    let different = lam(sort(l1()), bvar(0));
    assert!(!checker.def_eq(&lhs, &different));
}

// ========================================================================
// Translation tests
// ========================================================================

#[test]
fn test_translate_level_zero() {
    let kernel_level = Level::zero();
    let micro_level = MicroLevel::from_kernel(&kernel_level).unwrap();
    assert_eq!(micro_level, MicroLevel::Zero);
}

#[test]
fn test_translate_level_succ() {
    let kernel_level = Level::succ(Level::zero());
    let micro_level = MicroLevel::from_kernel(&kernel_level).unwrap();
    assert_eq!(micro_level, l1());
}

#[test]
fn test_translate_level_max() {
    // Note: Kernel Level::max simplifies max(0, l) = l
    // So we test with two non-comparable levels to get an actual Max

    // max(u, v) where u,v are parameters should NOT simplify
    // But since we can't translate params, test that max(1, 1) = 1
    let kernel_level = Level::max(Level::succ(Level::zero()), Level::succ(Level::zero()));
    let micro_level = MicroLevel::from_kernel(&kernel_level).unwrap();
    // max(1, 1) = 1 due to simplification
    assert_eq!(micro_level, l1());

    // Test that we can construct a Max if needed (raw construction)
    let raw_max = Level::Max(
        Level::succ(Level::zero()).into(),
        Level::succ(Level::succ(Level::zero())).into(),
    );
    let micro_max = MicroLevel::from_kernel(&raw_max).unwrap();
    // This should be Max(1, 2)
    assert_eq!(
        micro_max,
        MicroLevel::Max(Arc::new(l1()), Arc::new(MicroLevel::succ(l1())))
    );
}

#[test]
fn test_translate_level_param_fails() {
    use crate::name::Name;
    let kernel_level = Level::param(Name::from_string("u"));
    let err = MicroLevel::from_kernel(&kernel_level).unwrap_err();
    assert!(
        matches!(err, TranslateError::UnsupportedLevel(_)),
        "Level::param should fail with UnsupportedLevel, got: {err}"
    );
}

#[test]
fn test_translate_expr_sort() {
    let kernel_expr = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let micro_expr = MicroExpr::from_kernel(&kernel_expr).unwrap();
    assert_eq!(micro_expr, sort(l0()));
}

#[test]
fn test_translate_expr_bvar() {
    let kernel_expr = Expr::from_kind(ExprKind::BVar(5));
    let micro_expr = MicroExpr::from_kernel(&kernel_expr).unwrap();
    assert_eq!(micro_expr, bvar(5));
}

#[test]
fn test_translate_expr_lam() {
    use crate::expr::BinderInfo;

    // λ (x : Prop). x
    let kernel_expr = Expr::from_kind(ExprKind::Lam(
        BinderInfo::Default.into(),
        Arc::new(Expr::from_kind(ExprKind::Sort(Level::zero()))),
        Arc::new(Expr::from_kind(ExprKind::BVar(0))),
    ));
    let micro_expr = MicroExpr::from_kernel(&kernel_expr).unwrap();
    assert_eq!(micro_expr, lam(sort(l0()), bvar(0)));
}

#[test]
fn test_translate_expr_pi() {
    use crate::expr::BinderInfo;

    // Prop → Prop
    let kernel_expr = Expr::from_kind(ExprKind::Pi(
        BinderInfo::Default.into(),
        Arc::new(Expr::from_kind(ExprKind::Sort(Level::zero()))),
        Arc::new(Expr::from_kind(ExprKind::Sort(Level::zero()))),
    ));
    let micro_expr = MicroExpr::from_kernel(&kernel_expr).unwrap();
    assert_eq!(micro_expr, pi(sort(l0()), sort(l0())));
}

#[test]
fn test_translate_expr_app() {
    use crate::expr::BinderInfo;

    // (λ x. x) Prop
    let kernel_id = Expr::from_kind(ExprKind::Lam(
        BinderInfo::Default.into(),
        Arc::new(Expr::from_kind(ExprKind::Sort(Level::zero()))),
        Arc::new(Expr::from_kind(ExprKind::BVar(0))),
    ));
    let kernel_expr = Expr::from_kind(ExprKind::App(
        Arc::new(kernel_id),
        Arc::new(Expr::from_kind(ExprKind::Sort(Level::zero()))),
    ));
    let micro_expr = MicroExpr::from_kernel(&kernel_expr).unwrap();
    assert_eq!(micro_expr, app(lam(sort(l0()), bvar(0)), sort(l0())));
}

#[test]
fn test_translate_expr_const_fails() {
    use crate::name::Name;

    let kernel_expr = Expr::const_(Name::from_string("Nat"), vec![]);
    let err = MicroExpr::from_kernel(&kernel_expr).unwrap_err();
    assert!(
        matches!(err, TranslateError::UnsupportedExpr(_)),
        "Const should fail with UnsupportedExpr, got: {err}"
    );
}

#[test]
fn test_cross_validate_sort_verification() {
    // Verify that both micro-checker and main kernel agree on Sort typing
    use crate::env::Environment;
    use crate::tc::TypeChecker;

    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // Main kernel: Sort(0) : Sort(1)
    let kernel_expr = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let kernel_ty = tc.infer_type(&kernel_expr).unwrap();

    // Micro-checker
    let micro_expr = MicroExpr::from_kernel(&kernel_expr).unwrap();
    let micro_cert = MicroCert::Sort { level: l0() };
    let mut micro_checker = MicroChecker::new();
    let micro_ty = micro_checker.verify(&micro_cert, &micro_expr).unwrap();

    // Both should give Sort(1)
    let kernel_ty_translated = MicroExpr::from_kernel(&kernel_ty).unwrap();
    assert_eq!(micro_ty, kernel_ty_translated);
}

#[test]
fn test_cross_validate_identity_verification() {
    // Verify that both agree on identity function typing
    use crate::env::Environment;
    use crate::expr::BinderInfo;
    use crate::tc::TypeChecker;

    let env = Environment::new();
    let tc = TypeChecker::new(&env);

    // λ (x : Prop). x
    let kernel_expr = Expr::from_kind(ExprKind::Lam(
        BinderInfo::Default.into(),
        Arc::new(Expr::from_kind(ExprKind::Sort(Level::zero()))),
        Arc::new(Expr::from_kind(ExprKind::BVar(0))),
    ));
    let kernel_ty = tc.infer_type(&kernel_expr).unwrap();

    // Micro-checker
    let micro_expr = MicroExpr::from_kernel(&kernel_expr).unwrap();
    let micro_cert = MicroCert::Lam {
        arg_ty_cert: Box::new(MicroCert::Sort { level: l0() }),
        body_cert: Box::new(MicroCert::BVar {
            idx: 0,
            ty: Box::new(sort(l0())),
        }),
        result_ty: Box::new(pi(sort(l0()), sort(l0()))),
    };
    let mut micro_checker = MicroChecker::new();
    let micro_ty = micro_checker.verify(&micro_cert, &micro_expr).unwrap();

    // Both should give Prop → Prop
    let kernel_ty_translated = MicroExpr::from_kernel(&kernel_ty).unwrap();
    assert_eq!(micro_ty, kernel_ty_translated);
}

// ========================================================================
// cross_validate_with_micro error path tests
// ========================================================================

#[test]
fn test_cross_validate_detects_type_mismatch() {
    use crate::cert::ProofCert;

    // Expression: Sort(0)
    // Correct certificate: Sort(0) : Sort(1)
    // We'll claim the type is Sort(2) instead of Sort(1) to trigger disagreement
    let kernel_expr = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let wrong_inferred_type =
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::succ(Level::zero()))));
    let kernel_cert = ProofCert::Sort {
        level: Level::zero(),
    };
    let result = cross_validate_with_micro(&kernel_expr, &wrong_inferred_type, &kernel_cert);
    let err = result.expect_err("expected Err for micro-checker disagreement");
    let msg = err.to_string();
    assert!(
        msg.contains("MICRO-CHECKER DISAGREEMENT"),
        "expected MICRO-CHECKER DISAGREEMENT error, got: {msg}"
    );
}

#[test]
fn test_cross_validate_detects_verification_failure() {
    use crate::cert::ProofCert;

    // Expression: Sort(0)
    // Certificate claims it's a Sort with wrong level
    let kernel_expr = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let inferred_type = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));
    let wrong_cert = ProofCert::Sort {
        level: Level::succ(Level::zero()),
    };
    let result = cross_validate_with_micro(&kernel_expr, &inferred_type, &wrong_cert);
    let err = result.expect_err("expected Err for micro-checker verification failure");
    let msg = err.to_string();
    assert!(
        msg.contains("MICRO-CHECKER VERIFICATION FAILED"),
        "expected MICRO-CHECKER VERIFICATION FAILED error, got: {msg}"
    );
}

#[test]
fn test_cross_validate_returns_false_for_unsupported() {
    use crate::cert::ProofCert;
    use crate::name::Name;

    // Use a Const expression which micro-checker doesn't support
    let kernel_expr = Expr::const_(Name::from_string("Nat"), vec![]);
    let inferred_type = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let kernel_cert = ProofCert::Const {
        name: Name::from_string("Nat"),
        levels: vec![],
        type_: Box::new(Expr::from_kind(ExprKind::Sort(Level::zero()))),
    };

    // Should return Ok(false) (skipped)
    let result = cross_validate_with_micro(&kernel_expr, &inferred_type, &kernel_cert).unwrap();
    assert!(!result);
}

#[test]
fn test_cross_validate_returns_true_on_success() {
    use crate::cert::ProofCert;

    // Valid: Sort(0) : Sort(1)
    let kernel_expr = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let inferred_type = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));
    let kernel_cert = ProofCert::Sort {
        level: Level::zero(),
    };

    let result = cross_validate_with_micro(&kernel_expr, &inferred_type, &kernel_cert).unwrap();
    assert!(result);
}

// ========================================================================
// Tests targeting surviving mutations
// ========================================================================

// --- MicroExpr::lift arithmetic tests ---

#[test]
fn test_lift_bvar_at_cutoff() {
    // BVar(1) lifted at cutoff 1 with amount 1 should become BVar(2)
    let e = bvar(1);
    assert_eq!(e.lift(1, 1), bvar(2));
    // Below cutoff, unchanged
    assert_eq!(e.lift(2, 1), bvar(1));
}

#[test]
fn test_lift_pi_body_increment() {
    // Pi body has cutoff+1
    let e = pi(sort(l0()), bvar(1)); // body has free var at 1
    let lifted = e.lift(0, 1);
    // The body should lift with cutoff=1, so BVar(1) >= 1 becomes BVar(2)
    assert_eq!(lifted, pi(sort(l0()), bvar(2)));
}

#[test]
fn test_lift_let_body_increment() {
    // Let body has cutoff+1
    let e = let_(sort(l0()), sort(l0()), bvar(1)); // body has free var at 1
    let lifted = e.lift(0, 1);
    // The body should lift with cutoff=1, so BVar(1) >= 1 becomes BVar(2)
    assert_eq!(lifted, let_(sort(l0()), sort(l0()), bvar(2)));
}

#[test]
fn test_lift_multiple_amounts() {
    // Lifting by 2 vs lifting by 1 twice
    let e = bvar(0);
    let lift2 = e.lift(0, 2);
    assert_eq!(lift2, bvar(2));

    // Verify + vs * matters: lift(0, 2) should give BVar(0+2)=BVar(2), not BVar(0*2)=BVar(0)
    assert_ne!(lift2, bvar(0));
}

// --- MicroExpr::subst tests ---

#[test]
fn test_subst_boundary_condition() {
    // BVar(1) with depth=0: should become BVar(0) (idx > depth, so idx-1)
    let e = bvar(1);
    let val = sort(l0());
    let result = e.subst(0, &val);
    assert_eq!(result, bvar(0));
}

#[test]
fn test_subst_exact_match() {
    // BVar(0) with depth=0: should substitute
    let e = bvar(0);
    let val = sort(l1());
    let result = e.subst(0, &val);
    assert_eq!(result, val);
}

#[test]
fn test_subst_below_depth() {
    // BVar(0) with depth=1: idx < depth, so unchanged
    let e = bvar(0);
    let val = sort(l1());
    let result = e.subst(1, &val);
    assert_eq!(result, bvar(0));
}

#[test]
fn test_subst_body_depth_increment() {
    // Lambda body subst should use depth+1
    let e = lam(sort(l0()), bvar(1)); // Body refers to outer var (idx=1 after body's binder)
    let val = sort(l1());
    // Substituting at depth=0: body uses depth=1
    // BVar(1) in body: idx=1, depth=1, so idx == depth -> substitute
    let result = e.subst(0, &val);
    // The body's BVar(1) should be substituted with val.lift(0, 1) = sort(l1())
    assert_eq!(result, lam(sort(l0()), sort(l1())));
}

// --- MicroLevel::is_geq tests ---

#[test]
fn test_is_geq_same_base() {
    // If same base and offset1 >= offset2, return true
    let l1 = MicroLevel::succ(MicroLevel::succ(MicroLevel::Zero)); // 2
    let l2 = MicroLevel::succ(MicroLevel::Zero); // 1
    assert!(MicroLevel::is_geq(&l1, &l2)); // 2 >= 1
    assert!(!MicroLevel::is_geq(&l2, &l1)); // 1 >= 2 is false
}

#[test]
fn test_is_geq_equal_levels() {
    let l = MicroLevel::succ(MicroLevel::Zero);
    assert!(MicroLevel::is_geq(&l, &l)); // l >= l
}

#[test]
fn test_is_geq_zero_comparison() {
    // l >= 0 for any l
    let l = MicroLevel::succ(MicroLevel::Zero);
    assert!(MicroLevel::is_geq(&l, &MicroLevel::Zero));
    assert!(MicroLevel::is_geq(&MicroLevel::Zero, &MicroLevel::Zero));
}

#[test]
fn test_is_geq_offset_check() {
    // Test that offset > 0 check matters
    let l1 = MicroLevel::Succ(Arc::new(MicroLevel::Zero)); // 1
    let l2 = MicroLevel::Zero; // 0
                               // 1 >= 0 should be true
    assert!(MicroLevel::is_geq(&l1, &l2));

    // Verify the comparison is > not >=
    // offset1=1, l1' = Zero, check if Zero >= l2=Zero, which is true
    // But this relies on the comparison being >0, not >=0
}

#[test]
fn test_is_geq_max_left() {
    // max(a, b) >= l if a >= l or b >= l
    let a = MicroLevel::succ(MicroLevel::Zero); // 1
    let b = MicroLevel::Zero; // 0
    let max_level = MicroLevel::Max(Arc::new(a.clone()), Arc::new(b.clone()));
    let l = MicroLevel::succ(MicroLevel::Zero); // 1

    // max(1, 0) >= 1 should be true (because 1 >= 1)
    assert!(MicroLevel::is_geq(&max_level, &l));

    // max(0, 0) >= 1 should be false
    let max_zeros = MicroLevel::Max(Arc::new(MicroLevel::Zero), Arc::new(MicroLevel::Zero));
    assert!(!MicroLevel::is_geq(&max_zeros, &l));
}

#[test]
fn test_is_geq_max_right() {
    // l >= max(a, b) if l >= a and l >= b
    let l = MicroLevel::succ(MicroLevel::succ(MicroLevel::Zero)); // 2
    let a = MicroLevel::succ(MicroLevel::Zero); // 1
    let b = MicroLevel::succ(MicroLevel::Zero); // 1
    let max_level = MicroLevel::Max(Arc::new(a), Arc::new(b));

    // 2 >= max(1, 1) should be true
    assert!(MicroLevel::is_geq(&l, &max_level));

    // 0 >= max(1, 1) should be false
    assert!(!MicroLevel::is_geq(&MicroLevel::Zero, &max_level));

    // Test that AND is required: 1 >= max(0, 2) should be false
    let a2 = MicroLevel::Zero;
    let b2 = MicroLevel::succ(MicroLevel::succ(MicroLevel::Zero));
    let max2 = MicroLevel::Max(Arc::new(a2), Arc::new(b2));
    let one = MicroLevel::succ(MicroLevel::Zero);
    assert!(!MicroLevel::is_geq(&one, &max2)); // 1 >= 0 but 1 >= 2 is false
}

// --- MicroLevel::imax tests ---

#[test]
fn test_imax_zero_left() {
    // imax(0, l) = l (when l != 0)
    let l = MicroLevel::succ(MicroLevel::Zero);
    let result = MicroLevel::imax(MicroLevel::Zero, l.clone());
    assert_eq!(result, l);
}

#[test]
fn test_imax_equal() {
    // imax(l, l) = l
    let l = MicroLevel::succ(MicroLevel::Zero);
    let result = MicroLevel::imax(l.clone(), l.clone());
    assert_eq!(result, l);
}

#[test]
fn test_imax_creates_imax_node() {
    // When l2 is not Zero or Succ, and l1 != l2, should create IMax
    // Use an IMax as l2 to test this
    let l1 = MicroLevel::succ(MicroLevel::Zero);
    let inner = MicroLevel::IMax(
        Arc::new(MicroLevel::succ(MicroLevel::Zero)),
        Arc::new(MicroLevel::succ(MicroLevel::succ(MicroLevel::Zero))),
    );
    let result = MicroLevel::imax(l1.clone(), inner.clone());
    // Should create IMax(l1, inner) since inner is not Zero/Succ and l1 != inner
    assert!(matches!(result, MicroLevel::IMax(_, _)));
}

// --- MicroChecker::verify Opaque tests ---

#[test]
fn test_verify_opaque_matching_type() {
    let mut checker = MicroChecker::new();
    let ty = sort(l0());
    let expr = MicroExpr::Opaque(Arc::new(ty.clone()));
    let cert = MicroCert::Opaque {
        ty: Box::new(ty.clone()),
    };

    let verified_ty = checker
        .verify(&cert, &expr)
        .expect("Opaque with matching type should verify");
    assert_eq!(verified_ty, ty);
}

#[test]
fn test_verify_opaque_mismatching_type() {
    let mut checker = MicroChecker::new();
    let ty1 = sort(l0());
    let ty2 = sort(l1());
    let expr = MicroExpr::Opaque(Arc::new(ty1));
    let cert = MicroCert::Opaque { ty: Box::new(ty2) };

    let result = checker.verify(&cert, &expr);
    assert!(matches!(result, Err(MicroError::TypeMismatch { .. })));
}

/// Every recursive certificate edge must re-enter the segmented-stack guard.
/// A guard only at `verify`'s root still leaves one finite grown segment, which
/// adversarially deep (but structurally valid) projection certificates can
/// exhaust.
#[test]
fn test_verify_deep_projection_certificate_is_stack_safe() {
    const DEPTH: usize = 10_000;

    let ty = sort(l0());
    let mut expr = MicroExpr::Opaque(Arc::new(ty.clone()));
    let mut cert = MicroCert::Opaque {
        ty: Box::new(ty.clone()),
    };
    for _ in 0..DEPTH {
        expr = MicroExpr::Proj(0, Arc::new(expr));
        cert = MicroCert::Proj {
            idx: 0,
            expr_cert: Box::new(cert),
            field_ty: Box::new(ty.clone()),
        };
    }

    let mut checker = MicroChecker::new();
    assert_eq!(
        checker.verify(&cert, &expr),
        Ok(ty),
        "deep projection certificate should verify on the default test stack"
    );

    // Recursive Drop is a separate concern from verification and can obscure
    // this regression on platforms with especially small test-thread stacks.
    std::mem::forget(cert);
    std::mem::forget(expr);
}

// --- MicroChecker::structural_eq tests ---

#[test]
fn test_structural_eq_app() {
    let checker = MicroChecker::new();
    let f1 = sort(l0());
    let a1 = sort(l0());
    let app1 = app(f1.clone(), a1.clone());
    let app2 = app(f1.clone(), a1.clone());
    let app3 = app(f1.clone(), sort(l1())); // different arg
    let app4 = app(sort(l1()), a1.clone()); // different fn

    assert!(checker.structural_eq(&app1, &app2));
    assert!(!checker.structural_eq(&app1, &app3));
    assert!(!checker.structural_eq(&app1, &app4));
}

#[test]
fn test_structural_eq_pi() {
    let checker = MicroChecker::new();
    let pi1 = pi(sort(l0()), sort(l0()));
    let pi2 = pi(sort(l0()), sort(l0()));
    let pi3 = pi(sort(l1()), sort(l0())); // different type
    let pi4 = pi(sort(l0()), sort(l1())); // different body

    assert!(checker.structural_eq(&pi1, &pi2));
    assert!(!checker.structural_eq(&pi1, &pi3));
    assert!(!checker.structural_eq(&pi1, &pi4));
}

#[test]
fn test_structural_eq_let() {
    let checker = MicroChecker::new();
    let let1 = let_(sort(l0()), sort(l0()), bvar(0));
    let let2 = let_(sort(l0()), sort(l0()), bvar(0));
    let let3 = let_(sort(l1()), sort(l0()), bvar(0)); // different type
    let let4 = let_(sort(l0()), sort(l1()), bvar(0)); // different value
    let let5 = let_(sort(l0()), sort(l0()), bvar(1)); // different body

    assert!(checker.structural_eq(&let1, &let2));
    assert!(!checker.structural_eq(&let1, &let3));
    assert!(!checker.structural_eq(&let1, &let4));
    assert!(!checker.structural_eq(&let1, &let5));
}

#[test]
fn test_structural_eq_opaque() {
    let checker = MicroChecker::new();
    let op1 = MicroExpr::Opaque(Arc::new(sort(l0())));
    let op2 = MicroExpr::Opaque(Arc::new(sort(l0())));
    let op3 = MicroExpr::Opaque(Arc::new(sort(l1())));

    assert!(checker.structural_eq(&op1, &op2));
    assert!(!checker.structural_eq(&op1, &op3));
}

// --- Display tests ---

#[test]
fn test_micro_error_display() {
    let err = MicroError::InvalidBVar(5);
    let s = format!("{err}");
    assert!(!s.is_empty());

    let err2 = MicroError::StructureMismatch;
    let s2 = format!("{err2}");
    assert!(!s2.is_empty());
}

#[test]
fn test_translate_error_display() {
    let err = TranslateError::UnsupportedExpr("test".to_string());
    let s = format!("{err}");
    assert!(!s.is_empty());
    assert!(s.contains("test"));

    let err2 = TranslateError::UnsupportedLevel("level".to_string());
    let s2 = format!("{err2}");
    assert!(!s2.is_empty());
}

// =========================================================================
// Additional Mutation Testing Kill Tests - micro.rs survivors
// =========================================================================

#[test]
fn test_lift_plus_vs_times() {
    // Kill mutants: replace + with * in MicroExpr::lift (lines 180, 187)
    // Verify idx + amount, not idx * amount

    // BVar(2) lifted by 3 should be BVar(5), not BVar(6)
    let e = bvar(2);
    let lifted = e.lift(0, 3);
    assert_eq!(lifted, bvar(5), "2 + 3 = 5, not 2 * 3 = 6");

    // BVar(3) lifted by 2 should be BVar(5), not BVar(6)
    let e = bvar(3);
    let lifted = e.lift(0, 2);
    assert_eq!(lifted, bvar(5), "3 + 2 = 5, not 3 * 2 = 6");

    // BVar(1) lifted by 4 should be BVar(5), not BVar(4)
    let e = bvar(1);
    let lifted = e.lift(0, 4);
    assert_eq!(lifted, bvar(5), "1 + 4 = 5, not 1 * 4 = 4");
}

#[test]
fn test_subst_greater_than_vs_geq() {
    // Kill mutant: replace > with >= in MicroExpr::subst (line 205)
    // idx > depth means decrement, idx == depth means substitute

    // BVar(1) at depth 1: 1 == 1, so should substitute, NOT decrement
    let e = bvar(1);
    let val = sort(l1());
    let result = e.subst(1, &val);
    // val lifted by 1 = sort(l1())
    assert_eq!(result, sort(l1()), "BVar(1) at depth=1 should substitute");

    // BVar(2) at depth 1: 2 > 1, so should decrement to BVar(1)
    let e = bvar(2);
    let result = e.subst(1, &val);
    assert_eq!(
        result,
        bvar(1),
        "BVar(2) at depth=1 should decrement to BVar(1)"
    );
}

#[test]
fn test_subst_plus_vs_minus() {
    // Kill mutants: replace + with - in MicroExpr::subst (line 234)
    // Tests depth + 1 for nested binders

    // Lambda body uses depth+1 for substitution
    // λ (x : Prop). BVar(1) - in body, depth=1, so BVar(1)==1 gets substituted
    let e = lam(sort(l0()), bvar(1));
    let val = sort(l1());
    let result = e.subst(0, &val);
    // Body BVar(1) at depth=1: 1==1, substitute with val.lift(0,1) = sort(l1())
    assert_eq!(result, lam(sort(l0()), sort(l1())));

    // Pi also uses depth+1
    let e = pi(sort(l0()), bvar(1));
    let result = e.subst(0, &val);
    assert_eq!(result, pi(sort(l0()), sort(l1())));
}

#[test]
fn test_is_geq_comparison_operators() {
    // Kill mutants: replace > with ==, >=, < in MicroLevel::is_geq (line 295)
    // Tests offset1 > 0 comparison

    // Succ(Zero) vs Zero: offset1=1, base=Zero
    // offset1 > 0 means we check if Zero >= Zero (yes)
    // If > was ==: offset1 == 0 is false, wouldn't recurse
    // If > was <: offset1 < 0 is false, wouldn't recurse
    let l1 = MicroLevel::succ(MicroLevel::Zero); // offset=1
    let l0 = MicroLevel::Zero; // offset=0
    assert!(MicroLevel::is_geq(&l1, &l0), "Succ(Zero) >= Zero");

    // Succ(Succ(Zero)) vs Succ(Zero): 2 >= 1
    let l2 = MicroLevel::succ(MicroLevel::succ(MicroLevel::Zero));
    let l1_copy = MicroLevel::succ(MicroLevel::Zero);
    assert!(MicroLevel::is_geq(&l2, &l1_copy), "2 >= 1");

    // Zero vs Succ(Zero): 0 >= 1 should be false
    assert!(!MicroLevel::is_geq(&l0, &l1), "0 >= 1 is false");
}

#[test]
fn test_imax_equality_check() {
    // Kill mutant: replace == with != in MicroLevel::imax (line 344)
    // imax(l, l) = l, but if == became !=, identical levels wouldn't simplify

    // imax(Zero, Zero) should equal Zero
    let result = MicroLevel::imax(MicroLevel::Zero, MicroLevel::Zero);
    assert_eq!(result, MicroLevel::Zero);

    // imax(1, 1) should equal 1
    let l1 = MicroLevel::succ(MicroLevel::Zero);
    let result = MicroLevel::imax(l1.clone(), l1.clone());
    assert_eq!(result, l1);

    // imax(2, 2) should equal 2
    let l2 = MicroLevel::succ(MicroLevel::succ(MicroLevel::Zero));
    let result = MicroLevel::imax(l2.clone(), l2.clone());
    assert_eq!(result, l2);
}

// =========================================================================
// Additional Mutation Kill Tests - cutoff+1 and depth+1
// =========================================================================

#[test]
fn test_lift_cutoff_plus_one_in_binders() {
    // Kill mutants at lines 180, 187: replace cutoff + 1 with cutoff * 1
    // When cutoff=0, cutoff+1=1 vs cutoff*1=0 behaves differently

    // λ x. BVar(0) lifted at cutoff 0 by 5
    // Under lambda, cutoff becomes 0+1=1
    // BVar(0) < 1, so NOT lifted (it's bound)
    // With * mutant: cutoff*1=0, BVar(0) >= 0, WOULD lift (wrong!)
    let e = lam(sort(l0()), bvar(0));
    let result = e.lift(0, 5);
    match &result {
        MicroExpr::Lam(_, body) => {
            assert_eq!(
                body.as_ref(),
                &bvar(0),
                "BVar(0) under lambda should NOT be lifted (bound)"
            );
        }
        _ => panic!("Expected Lam"),
    }

    // λ x. BVar(1) lifted at cutoff 0 by 5
    // Under lambda, cutoff=1. BVar(1) >= 1, so lifted to BVar(6)
    let e = lam(sort(l0()), bvar(1));
    let result = e.lift(0, 5);
    match &result {
        MicroExpr::Lam(_, body) => {
            assert_eq!(
                body.as_ref(),
                &bvar(6),
                "BVar(1) under lambda should be lifted to BVar(6)"
            );
        }
        _ => panic!("Expected Lam"),
    }

    // Pi: same behavior
    let e = pi(sort(l0()), bvar(0));
    let result = e.lift(0, 5);
    match &result {
        MicroExpr::Pi(_, body) => {
            assert_eq!(
                body.as_ref(),
                &bvar(0),
                "BVar(0) under Pi should NOT be lifted"
            );
        }
        _ => panic!("Expected Pi"),
    }

    // Let body: cutoff+1
    let e = let_(sort(l0()), sort(l0()), bvar(0));
    let result = e.lift(0, 5);
    match &result {
        MicroExpr::Let(_, _, body) => {
            assert_eq!(
                body.as_ref(),
                &bvar(0),
                "BVar(0) under let body should NOT be lifted"
            );
        }
        _ => panic!("Expected Let"),
    }

    // Double nested: λ x. λ y. BVar(1)
    // At depth 2, cutoff=2. BVar(1) < 2, not lifted
    let inner = lam(sort(l0()), bvar(1));
    let outer = lam(sort(l0()), inner);
    let result = outer.lift(0, 5);
    // Navigate to innermost
    match &result {
        MicroExpr::Lam(_, body) => match body.as_ref() {
            MicroExpr::Lam(_, inner_body) => {
                assert_eq!(
                    inner_body.as_ref(),
                    &bvar(1),
                    "BVar(1) under 2 lambdas should NOT be lifted"
                );
            }
            _ => panic!("Expected inner Lam"),
        },
        _ => panic!("Expected outer Lam"),
    }

    // λ x. λ y. BVar(2) at depth 2 IS >= 2, so lifted to BVar(7)
    let inner = lam(sort(l0()), bvar(2));
    let outer = lam(sort(l0()), inner);
    let result = outer.lift(0, 5);
    match &result {
        MicroExpr::Lam(_, body) => match body.as_ref() {
            MicroExpr::Lam(_, inner_body) => {
                assert_eq!(
                    inner_body.as_ref(),
                    &bvar(7),
                    "BVar(2) under 2 lambdas should be lifted to BVar(7)"
                );
            }
            _ => panic!("Expected inner Lam"),
        },
        _ => panic!("Expected outer Lam"),
    }
}

#[test]
fn test_subst_depth_plus_one_in_binders() {
    // Kill mutants at line 234: replace depth + 1 with depth * 1 or depth - 1
    // When depth=0, depth+1=1 vs depth*1=0 behaves differently

    // λ x. BVar(0) substituted at depth 0
    // Body at depth 0+1=1. BVar(0) < 1, stays as is
    // With * mutant: depth*1=0, BVar(0)==0, would substitute (wrong!)
    let e = lam(sort(l0()), bvar(0));
    let val = sort(l1());
    let result = e.subst(0, &val);
    match &result {
        MicroExpr::Lam(_, body) => {
            assert_eq!(
                body.as_ref(),
                &bvar(0),
                "BVar(0) under lambda should stay (bound to lambda param)"
            );
        }
        _ => panic!("Expected Lam"),
    }

    // λ x. BVar(1) substituted at depth 0
    // Body at depth 1. BVar(1)==1, substitutes with val.lift(0,1)
    let e = lam(sort(l0()), bvar(1));
    let result = e.subst(0, &val);
    match &result {
        MicroExpr::Lam(_, body) => {
            // val.lift(0,1) = sort(l1()) since no bvars
            assert_eq!(
                body.as_ref(),
                &sort(l1()),
                "BVar(1) under lambda at depth 0 substitutes"
            );
        }
        _ => panic!("Expected Lam"),
    }

    // λ x. BVar(2) substituted at depth 0
    // Body at depth 1. BVar(2) > 1, decrements to BVar(1)
    let e = lam(sort(l0()), bvar(2));
    let result = e.subst(0, &val);
    match &result {
        MicroExpr::Lam(_, body) => {
            assert_eq!(
                body.as_ref(),
                &bvar(1),
                "BVar(2) under lambda at depth 0 decrements to BVar(1)"
            );
        }
        _ => panic!("Expected Lam"),
    }

    // let x = v in BVar(0): body at depth+1
    let e = let_(sort(l0()), sort(l0()), bvar(0));
    let result = e.subst(0, &val);
    match &result {
        MicroExpr::Let(_, _, body) => {
            assert_eq!(
                body.as_ref(),
                &bvar(0),
                "BVar(0) under let should stay (bound to let)"
            );
        }
        _ => panic!("Expected Let"),
    }

    // Double nested: λ x. λ y. BVar(2)
    // At depth 2, BVar(2)==2 substitutes
    let inner = lam(sort(l0()), bvar(2));
    let outer = lam(sort(l0()), inner);
    let result = outer.subst(0, &val);
    match &result {
        MicroExpr::Lam(_, body) => match body.as_ref() {
            MicroExpr::Lam(_, inner_body) => {
                // val.lift(0,2) = sort(l1()) since no bvars
                assert_eq!(
                    inner_body.as_ref(),
                    &sort(l1()),
                    "BVar(2) under 2 lambdas at depth 0 substitutes"
                );
            }
            _ => panic!("Expected inner Lam"),
        },
        _ => panic!("Expected outer Lam"),
    }
}

#[test]
fn test_subst_gt_not_gte() {
    // Kill mutant at line 205: replace > with >= in subst
    // When idx == depth, we substitute. When idx > depth, we decrement.

    // BVar(0) at depth 0: idx==depth, SUBSTITUTE
    let e = bvar(0);
    let val = sort(l1());
    let result = e.subst(0, &val);
    assert_eq!(
        result,
        sort(l1()),
        "BVar(0) at depth 0: == case, should substitute"
    );

    // BVar(1) at depth 0: idx > depth, DECREMENT to BVar(0)
    let e = bvar(1);
    let result = e.subst(0, &val);
    assert_eq!(
        result,
        bvar(0),
        "BVar(1) at depth 0: > case, should decrement"
    );

    // BVar(0) at depth 0 but val has structure
    let complex_val = app(sort(l0()), sort(l1()));
    let result = bvar(0).subst(0, &complex_val);
    assert_eq!(
        result, complex_val,
        "Substitution should return val exactly at depth 0"
    );
}

#[test]
fn test_is_geq_offset_gt_zero() {
    // Kill mutants at line 295: replace > with ==, >=, or <
    // offset1 > 0 check for Succ levels

    // Create Max level to test where bases differ but offset > 0 matters
    let max_ab = MicroLevel::Max(
        Arc::new(MicroLevel::Zero),
        Arc::new(MicroLevel::succ(MicroLevel::Zero)),
    );

    // succ(max(0, 1)) >= max(0, 1)
    // l1 = Succ(max), l2 = max
    // bases differ, but offset1=1 > 0, so check max >= max (true via same level)
    let succ_max = MicroLevel::succ(max_ab.clone());
    assert!(
        MicroLevel::is_geq(&succ_max, &max_ab),
        "succ(max(0,1)) >= max(0,1) via offset > 0 recursive check"
    );

    // For the > vs >= case at offset checking:
    // When offset1 = 1 and we're checking recursively:
    // > 0: 1 > 0 is true, does the recursive check
    // >= 0: 1 >= 0 is true, would ALSO do recursive check (same result here)
    // == 0: 1 == 0 is false, wouldn't recurse
    // < 0: 1 < 0 is false, wouldn't recurse

    // For offset1 = 0 case:
    // > 0: 0 > 0 is false, skip recursive check
    // >= 0: 0 >= 0 is true, would recurse (different!)
    // == 0: 0 == 0 is true, would recurse (different!)
    // < 0: 0 < 0 is false, skip

    // So we need a case where offset1 = 0 but the recursive check matters
    // But if offset1=0, then l1 has no Succ wrapper, so as_inner() would
    // just return l1 itself... Actually let me re-read the code

    // offset1 > 0 means the level has at least one Succ wrapper
    // So the check is: if l1 = succ^k(l1') with k > 0, then check l1' >= l2
    // If k = 0, we skip this optimization

    // To kill > vs == mutation: need case where offset=1 makes difference
    // To kill > vs < mutation: offset < 0 is never true for u32, always skipped
    // To kill > vs >= mutation: need offset=0 case where >= would recurse but > wouldn't

    // But offset=0 means no Succ, so l1_inner = l1, checking l1 >= l2 is circular...
    // Actually looking at code:
    // if offset1 > 0 { if is_geq(l1.as_inner(), l2) { return true; } }
    // as_inner removes one Succ layer
    // So this only makes sense when offset1 >= 1

    // Key test: does > vs >= matter?
    // When offset1 = 0: > 0 is false, skip. >= 0 is true, would check as_inner
    // But as_inner of a non-Succ level just returns itself, leading to infinite recursion
    // So >= 0 would cause issues, > 0 is correct

    // We can't directly test >= vs > with offset=0 because it would loop
    // But the test above with offset=1 shows the code path works
}

#[test]
fn test_imax_eq_vs_ne() {
    // Kill mutant at line 344: replace == with != in MicroLevel::imax
    // imax(l1, l2) when l1 == l2 should return l1

    // Max levels
    let max_01 = MicroLevel::Max(
        Arc::new(MicroLevel::Zero),
        Arc::new(MicroLevel::succ(MicroLevel::Zero)),
    );

    // imax(max(0,1), max(0,1)) should return max(0,1)
    // With != mutation: l1 != l2 is false, wouldn't simplify
    let result = MicroLevel::imax(max_01.clone(), max_01.clone());
    assert_eq!(
        result, max_01,
        "imax(l, l) should return l when both are equal Max levels"
    );

    // IMax level
    let imax_01 = MicroLevel::IMax(
        Arc::new(MicroLevel::Zero),
        Arc::new(MicroLevel::succ(MicroLevel::Zero)),
    );

    // imax(imax(0,1), imax(0,1)) should return imax(0,1)
    let result = MicroLevel::imax(imax_01.clone(), imax_01.clone());
    assert_eq!(
        result, imax_01,
        "imax(l, l) should return l when both are equal IMax levels"
    );
}

#[test]
fn test_is_geq_offset_with_different_bases() {
    // Kill mutants at line 295: replace > with <, ==, or >=
    // This test uses levels with DIFFERENT bases to distinguish mutations
    //
    // succ(max(0, 1)) >= 1
    // l1 = succ(max(0, 1)), l2 = succ(0)
    // get_offset(l1) = (max(0, 1), 1)
    // get_offset(l2) = (Zero, 1)
    // bases differ: max(0, 1) != Zero
    //
    // With > 0: offset1=1 > 0, check is_geq(max(0, 1), succ(0))
    //   max(a, b) >= l if a >= l or b >= l
    //   0 >= 1? false. 1 >= 1? true via same offset
    //   Returns true
    // With < 0: 1 < 0 is false, skip offset check
    //   l1 is Succ not Max, skip max check
    //   l2 is Succ(Zero) not Max, skip max check
    //   Return false (WRONG!)
    let max_01 = MicroLevel::Max(
        Arc::new(MicroLevel::Zero),
        Arc::new(MicroLevel::succ(MicroLevel::Zero)),
    );
    let succ_max = MicroLevel::succ(max_01);
    let one = MicroLevel::succ(MicroLevel::Zero);

    assert!(
        MicroLevel::is_geq(&succ_max, &one),
        "succ(max(0, 1)) >= 1 should be true: bases differ but inner max(0,1) >= 1"
    );
}

#[test]
fn test_imax_zero_left_returns_right() {
    // Kill mutant at line 344: replace == with != in check for l1 == Zero
    // imax(0, l) = l (when l != 0)
    //
    // With ==: l1 == Zero is true, return l2
    // With !=: l1 != Zero is false, skip this check
    //   Then l1 == l2? 0 != IMax, so false
    //   Would return IMax(0, IMax(...))
    let inner = MicroLevel::IMax(
        Arc::new(MicroLevel::Zero),
        Arc::new(MicroLevel::succ(MicroLevel::Zero)),
    );

    // imax(0, imax(0, 1)) should return imax(0, 1)
    let result = MicroLevel::imax(MicroLevel::Zero, inner.clone());
    assert_eq!(
        result, inner,
        "imax(0, l) should return l directly when l is non-zero IMax"
    );
}

#[test]
fn test_get_offset_nested_succ() {
    // Kill mutant at line 321: delete match arm MicroLevel::Succ
    // get_offset should recursively unwrap Succ to count the offset
    //
    // With Succ arm: succ(succ(Zero)) -> (Zero, 2)
    // Without Succ arm (using _ =>): succ(succ(Zero)) -> (succ(succ(Zero)), 0)
    //
    // Test is_geq uses get_offset, so we test via is_geq:
    // succ(succ(Zero)) >= succ(Zero)?
    // With correct get_offset: bases both Zero, offsets 2 >= 1, true
    // With broken get_offset: bases differ, would check different paths
    let two = MicroLevel::succ(MicroLevel::succ(MicroLevel::Zero));
    let one = MicroLevel::succ(MicroLevel::Zero);

    assert!(
        MicroLevel::is_geq(&two, &one),
        "succ(succ(0)) >= succ(0) should be true - offset 2 >= 1"
    );

    // Also test that succ(succ(succ(Zero))) >= succ(Zero)
    let three = MicroLevel::succ(MicroLevel::succ(MicroLevel::succ(MicroLevel::Zero)));
    assert!(
        MicroLevel::is_geq(&three, &one),
        "succ(succ(succ(0))) >= succ(0) should be true - offset 3 >= 1"
    );
}

// =========================================================================
// Kill: micro.rs:233:47 - Let body in subst (depth + 1)
// =========================================================================
#[test]
fn test_micro_subst_let_body_depth() {
    // This tests that the Let body correctly increments depth by 1
    // Mutation: depth + 1 -> depth - 1 should fail

    // let x = Prop in BVar(1) - BVar(1) at depth 1 should be substituted
    let val = MicroExpr::Sort(MicroLevel::succ(MicroLevel::Zero)); // Type 1
    let let_expr = MicroExpr::Let(
        Arc::new(MicroExpr::Sort(MicroLevel::Zero)), // type: Prop
        Arc::new(MicroExpr::Sort(MicroLevel::Zero)), // value: Prop
        Arc::new(MicroExpr::BVar(1)),                // body: BVar(1)
    );
    let result = let_expr.subst(0, &val);
    match &result {
        MicroExpr::Let(_, _, body) => {
            // BVar(1) at depth 1: 1 == 1, so substitute with val (no lifting needed)
            assert!(
                matches!(body.as_ref(), MicroExpr::Sort(MicroLevel::Succ(_))),
                "BVar(1) in let body should be substituted at depth 1"
            );
        }
        _ => panic!("Expected Let"),
    }

    // let x = Prop in BVar(0) - BVar(0) at depth 1 is the let-bound variable
    // Should NOT be substituted (0 < 1)
    let let_expr = MicroExpr::Let(
        Arc::new(MicroExpr::Sort(MicroLevel::Zero)),
        Arc::new(MicroExpr::Sort(MicroLevel::Zero)),
        Arc::new(MicroExpr::BVar(0)),
    );
    let result = let_expr.subst(0, &val);
    match &result {
        MicroExpr::Let(_, _, body) => {
            assert!(
                matches!(body.as_ref(), MicroExpr::BVar(0)),
                "BVar(0) in let body refers to let binding, not substituted"
            );
        }
        _ => panic!("Expected Let"),
    }
}

// =========================================================================
// Kill: micro.rs:256:15, 259:15 - == vs != in MicroLevel::max
// =========================================================================
#[test]
fn test_micro_level_max_zero_checks() {
    // Kill mutants: l1 == MicroLevel::Zero and l2 == MicroLevel::Zero with !=
    //
    // max(0, l) = l
    // max(l, 0) = l

    // max(0, succ(0)) = succ(0), not max(0, succ(0))
    let zero = MicroLevel::Zero;
    let one = MicroLevel::succ(MicroLevel::Zero);

    let result = MicroLevel::max(zero.clone(), one.clone());
    assert_eq!(result, one.clone(), "max(0, 1) should return 1 directly");

    // max(succ(0), 0) = succ(0)
    let result = MicroLevel::max(one.clone(), zero.clone());
    assert_eq!(result, one, "max(1, 0) should return 1 directly");

    // Important: test that we DON'T simplify incorrectly
    // With mutation: != instead of ==, max(0, 1) would not trigger the simplification
    // and would fall through to is_geq checks or return Max(0, 1)

    // Check that a non-zero max doesn't trigger zero simplification
    let two = MicroLevel::succ(MicroLevel::succ(MicroLevel::Zero));
    let result = MicroLevel::max(one.clone(), two.clone());
    assert_eq!(result, two, "max(1, 2) should return 2 via is_geq");
}

// =========================================================================
// Kill: micro.rs:321 - delete Succ arm in get_offset
// =========================================================================
#[test]
fn test_get_offset_direct() {
    // Direct unit test for get_offset to kill the "delete Succ arm" mutant.
    // If Succ arm is deleted, get_offset returns (self, 0) for all inputs.
    //
    // With Succ arm: succ(succ(Zero)) -> (&Zero, 2)
    // Without Succ arm: succ(succ(Zero)) -> (&succ(succ(Zero)), 0)

    let zero = MicroLevel::Zero;
    let one = MicroLevel::succ(MicroLevel::Zero);
    let two = MicroLevel::succ(MicroLevel::succ(MicroLevel::Zero));
    let three = MicroLevel::succ(MicroLevel::succ(MicroLevel::succ(MicroLevel::Zero)));

    // Test Zero: should return (Zero, 0)
    let (base, offset) = MicroLevel::get_offset(&zero);
    assert_eq!(*base, MicroLevel::Zero);
    assert_eq!(offset, 0, "Zero should have offset 0");

    // Test succ(Zero): should return (Zero, 1)
    let (base, offset) = MicroLevel::get_offset(&one);
    assert_eq!(*base, MicroLevel::Zero, "succ(0) base should be Zero");
    assert_eq!(offset, 1, "succ(0) should have offset 1");

    // Test succ(succ(Zero)): should return (Zero, 2)
    let (base, offset) = MicroLevel::get_offset(&two);
    assert_eq!(*base, MicroLevel::Zero, "succ(succ(0)) base should be Zero");
    assert_eq!(offset, 2, "succ(succ(0)) should have offset 2");

    // Test succ(succ(succ(Zero))): should return (Zero, 3)
    let (base, offset) = MicroLevel::get_offset(&three);
    assert_eq!(
        *base,
        MicroLevel::Zero,
        "succ(succ(succ(0))) base should be Zero"
    );
    assert_eq!(offset, 3, "succ(succ(succ(0))) should have offset 3");

    // Test with a Max base: succ(succ(Max(0,0))) -> (Max(0,0), 2)
    let max_base = MicroLevel::Max(Arc::new(MicroLevel::Zero), Arc::new(MicroLevel::Zero));
    let max_plus_2 = MicroLevel::succ(MicroLevel::succ(max_base.clone()));
    let (base, offset) = MicroLevel::get_offset(&max_plus_2);
    assert_eq!(
        *base, max_base,
        "succ(succ(Max(0,0))) base should be Max(0,0)"
    );
    assert_eq!(offset, 2, "succ(succ(Max(0,0))) should have offset 2");
}

// ========================================================================
// Overflow Protection Tests
// ========================================================================

#[test]
fn test_lift_overflow_at_u32_max_saturates() {
    // BVar(u32::MAX).lift(0, 1) saturates at u32::MAX instead of panicking
    let e = MicroExpr::BVar(u32::MAX);
    let result = e.lift(0, 1);
    assert_eq!(result, MicroExpr::BVar(u32::MAX));
}

#[test]
fn test_lift_cutoff_overflow_saturates() {
    // When cutoff == u32::MAX, entering Lam body saturates cutoff;
    // no BVars have index >= u32::MAX so body is unchanged
    let e = lam(sort(l0()), bvar(0));
    let result = e.lift(u32::MAX, 1);
    assert_eq!(result, lam(sort(l0()), bvar(0)));
}

#[test]
fn test_subst_depth_overflow_saturates() {
    // When depth == u32::MAX, entering Lam body saturates depth;
    // no BVars match depth == u32::MAX so body is unchanged
    let e = lam(sort(l0()), bvar(0));
    let val = sort(l1());
    let result = e.subst(u32::MAX, &val);
    assert_eq!(result, lam(sort(l0()), bvar(0)));
}

#[test]
fn test_get_offset_does_not_overflow_in_normal_use() {
    // Normal levels should work fine - get_offset is protected
    let l = MicroLevel::succ(MicroLevel::succ(MicroLevel::Zero));
    let (base, offset) = MicroLevel::get_offset(&l);
    assert_eq!(*base, MicroLevel::Zero);
    assert_eq!(offset, 2);
}

#[test]
fn test_subst_pi_depth_overflow_saturates() {
    // When depth == u32::MAX, entering Pi body saturates depth;
    // body is unchanged since no BVars match
    let e = pi(sort(l0()), bvar(0));
    let val = sort(l1());
    let result = e.subst(u32::MAX, &val);
    assert_eq!(result, pi(sort(l0()), bvar(0)));
}

#[test]
fn test_subst_let_depth_overflow_saturates() {
    // When depth == u32::MAX, entering Let body saturates depth;
    // body is unchanged since no BVars match
    let e = MicroExpr::Let(Arc::new(sort(l0())), Arc::new(bvar(0)), Arc::new(bvar(1)));
    let val = sort(l1());
    let result = e.subst(u32::MAX, &val);
    assert_eq!(
        result,
        MicroExpr::Let(Arc::new(sort(l0())), Arc::new(bvar(0)), Arc::new(bvar(1)))
    );
}

#[test]
fn test_lift_pi_cutoff_overflow_saturates() {
    // When cutoff == u32::MAX, entering Pi body saturates cutoff;
    // body is unchanged since no BVars >= u32::MAX
    let e = pi(sort(l0()), bvar(0));
    let result = e.lift(u32::MAX, 1);
    assert_eq!(result, pi(sort(l0()), bvar(0)));
}

#[test]
fn test_lift_let_cutoff_overflow_saturates() {
    // When cutoff == u32::MAX, entering Let body saturates cutoff;
    // body is unchanged since no BVars >= u32::MAX
    let e = MicroExpr::Let(Arc::new(sort(l0())), Arc::new(bvar(0)), Arc::new(bvar(1)));
    let result = e.lift(u32::MAX, 1);
    assert_eq!(
        result,
        MicroExpr::Let(Arc::new(sort(l0())), Arc::new(bvar(0)), Arc::new(bvar(1)))
    );
}

// ========================================================================
// Lit/Proj tests (#1261)
// ========================================================================

#[test]
fn test_micro_literal_from_kernel_nat_small() {
    use crate::expr::{BigNat, Literal};
    let lit = Literal::Nat(BigNat::Small(42));
    let result = MicroLiteral::from_kernel(&lit).unwrap();
    assert_eq!(result, MicroLiteral::nat_u64(42));
}

#[test]
fn test_micro_literal_from_kernel_nat_big_supported() {
    // The micro-checker now uses its OWN arbitrary-precision BigUint, so a
    // multi-limb BigNat translates faithfully (no u64 cap). Limbs are
    // little-endian: [1, 2, 3] = 1 + 2*2^64 + 3*2^128.
    use crate::expr::{BigNat, Literal};
    use num_bigint::BigUint;
    let lit = Literal::Nat(BigNat::Big(vec![1, 2, 3]));
    let result = MicroLiteral::from_kernel(&lit).unwrap();
    let expected = BigUint::from(1u64) + (BigUint::from(2u64) << 64) + (BigUint::from(3u64) << 128);
    assert_eq!(result, MicroLiteral::Nat(expected));
}

#[test]
fn test_micro_literal_from_kernel_string() {
    use crate::expr::Literal;
    let lit = Literal::String(Arc::from("hello"));
    let result = MicroLiteral::from_kernel(&lit).unwrap();
    assert_eq!(result, MicroLiteral::String(Arc::from("hello")));
}

#[test]
fn test_lit_lift_is_noop() {
    let e = lit_nat(42);
    assert_eq!(e.lift(0, 5), e);
    assert_eq!(e.lift(10, 1), e);
}

#[test]
fn test_lit_subst_is_noop() {
    let e = lit_nat(99);
    let replacement = sort(l1());
    assert_eq!(e.subst(0, &replacement), e);
    assert_eq!(e.subst(5, &replacement), e);
}

#[test]
fn test_proj_lift_propagates() {
    // proj(0, bvar(0)) with lift(0, 1) => proj(0, bvar(1))
    let e = proj(0, bvar(0));
    let lifted = e.lift(0, 1);
    assert_eq!(lifted, proj(0, bvar(1)));
}

#[test]
fn test_proj_subst_propagates() {
    // proj(1, bvar(0)) with subst(0, Sort(0)) => proj(1, Sort(0))
    let e = proj(1, bvar(0));
    let result = e.subst(0, &sort(l0()));
    assert_eq!(result, proj(1, sort(l0())));
}

#[test]
fn test_structural_eq_lit_same() {
    let checker = MicroChecker::new();
    assert!(checker.structural_eq(&lit_nat(42), &lit_nat(42)));
    assert!(checker.structural_eq(&lit_str("abc"), &lit_str("abc")));
}

#[test]
fn test_structural_eq_lit_different() {
    let checker = MicroChecker::new();
    assert!(!checker.structural_eq(&lit_nat(1), &lit_nat(2)));
    assert!(!checker.structural_eq(&lit_str("a"), &lit_str("b")));
    assert!(!checker.structural_eq(&lit_nat(0), &lit_str("0")));
}

#[test]
fn test_structural_eq_proj_same() {
    let checker = MicroChecker::new();
    let a = proj(0, sort(l0()));
    let b = proj(0, sort(l0()));
    assert!(checker.structural_eq(&a, &b));
}

#[test]
fn test_structural_eq_proj_different_idx() {
    let checker = MicroChecker::new();
    let a = proj(0, sort(l0()));
    let b = proj(1, sort(l0()));
    assert!(!checker.structural_eq(&a, &b));
}

#[test]
fn test_structural_eq_proj_different_inner() {
    let checker = MicroChecker::new();
    let a = proj(0, sort(l0()));
    let b = proj(0, sort(l1()));
    assert!(!checker.structural_eq(&a, &b));
}

#[test]
fn test_verify_lit_cert() {
    let mut checker = MicroChecker::new();
    let nat_ty = sort(l1()); // Stand-in for Nat type
    let expr = lit_nat(42);
    let cert = MicroCert::Lit {
        lit: MicroLiteral::nat_u64(42),
        ty: Box::new(nat_ty.clone()),
    };
    let verified_ty = checker
        .verify(&cert, &expr)
        .expect("Lit cert with matching literal should verify");
    assert_eq!(verified_ty, nat_ty);
}

#[test]
fn test_verify_lit_cert_mismatch() {
    let mut checker = MicroChecker::new();
    let expr = lit_nat(42);
    let cert = MicroCert::Lit {
        lit: MicroLiteral::nat_u64(99), // wrong literal
        ty: Box::new(sort(l1())),
    };
    let err = checker.verify(&cert, &expr).unwrap_err();
    assert!(
        matches!(err, MicroError::StructureMismatch),
        "Mismatched literal should give StructureMismatch, got: {err}"
    );
}

#[test]
fn test_verify_proj_cert() {
    let mut checker = MicroChecker::new();
    let field_ty = sort(l0());
    // proj(0, Sort(1)) with cert for inner = Sort(1) : Sort(2)
    let inner_cert = MicroCert::Sort { level: l1() };
    let expr = proj(0, sort(l1()));
    let cert = MicroCert::Proj {
        idx: 0,
        expr_cert: Box::new(inner_cert),
        field_ty: Box::new(field_ty.clone()),
    };
    let verified_ty = checker
        .verify(&cert, &expr)
        .expect("Proj cert with matching index should verify");
    assert_eq!(verified_ty, field_ty);
}

#[test]
fn test_verify_proj_cert_idx_mismatch() {
    let mut checker = MicroChecker::new();
    let inner_cert = MicroCert::Sort { level: l1() };
    let expr = proj(0, sort(l1()));
    let cert = MicroCert::Proj {
        idx: 1, // wrong index
        expr_cert: Box::new(inner_cert),
        field_ty: Box::new(sort(l0())),
    };
    let err = checker.verify(&cert, &expr).unwrap_err();
    assert!(
        matches!(err, MicroError::StructureMismatch),
        "Proj index mismatch should give StructureMismatch, got: {err}"
    );
}

// ========================================================================
// Recursor IOTA tests (Bool.rec / Nat.rec / Bool.beq) — the increment-2
// additions. These exercise the micro-checker's OWN recursor engine
// (`checker::reduce_recursor`) directly; they never call the kernel reducer.
// ========================================================================

mod recursor_iota {
    use super::*;
    use crate::micro::{MicroConst, MicroEnv};

    fn const_(name: &str) -> MicroExpr {
        MicroExpr::Const(Arc::from(name))
    }
    fn bool_const(b: bool) -> MicroExpr {
        const_(if b { "Bool.true" } else { "Bool.false" })
    }
    fn nat_ty() -> MicroExpr {
        const_("Nat")
    }
    fn bool_ty() -> MicroExpr {
        const_("Bool")
    }

    /// Build an env modeling the prelude's `Bool.not`/`Bool.and` as their real
    /// `Bool.rec` bodies (reducible defs), so the checker reduces them by DELTA
    /// + its OWN `Bool.rec` IOTA — the same path the kernel takes.
    fn bool_env() -> MicroEnv {
        let mut env = MicroEnv::new();
        let bb = || bool_ty();
        // motive: λ _ : Bool => Bool
        let motive = lam(bb(), bb());
        // Bool.not := λ b => @Bool.rec motive Bool.true Bool.false b
        // (minor order: false-case, true-case).
        let not_body = lam(
            bb(),
            MicroExpr::App(
                Arc::new(MicroExpr::App(
                    Arc::new(MicroExpr::App(
                        Arc::new(MicroExpr::App(
                            Arc::new(const_("Bool.rec")),
                            Arc::new(motive.clone()),
                        )),
                        Arc::new(bool_const(true)),
                    )),
                    Arc::new(bool_const(false)),
                )),
                Arc::new(bvar(0)),
            ),
        );
        env.insert(
            "Bool.not",
            MicroConst {
                ty: pi(bb(), bb()),
                body: Some(not_body),
            },
        );
        // Bool.and := λ a b => @Bool.rec motive Bool.false b a
        let and_body = lam(
            bb(),
            lam(
                bb(),
                MicroExpr::App(
                    Arc::new(MicroExpr::App(
                        Arc::new(MicroExpr::App(
                            Arc::new(MicroExpr::App(
                                Arc::new(const_("Bool.rec")),
                                Arc::new(motive.clone()),
                            )),
                            Arc::new(bool_const(false)),
                        )),
                        Arc::new(bvar(0)), // b
                    )),
                    Arc::new(bvar(1)), // a
                ),
            ),
        );
        env.insert(
            "Bool.and",
            MicroConst {
                ty: pi(bb(), pi(bb(), bb())),
                body: Some(and_body),
            },
        );
        env
    }

    /// `@Bool.rec (λ _ => Nat) zero_case one_case major` — a NAT-valued cond.
    fn cond_nat(major: MicroExpr, false_case: MicroExpr, true_case: MicroExpr) -> MicroExpr {
        let motive = lam(bool_ty(), nat_ty());
        MicroExpr::App(
            Arc::new(MicroExpr::App(
                Arc::new(MicroExpr::App(
                    Arc::new(MicroExpr::App(
                        Arc::new(const_("Bool.rec")),
                        Arc::new(motive),
                    )),
                    Arc::new(false_case),
                )),
                Arc::new(true_case),
            )),
            Arc::new(major),
        )
    }

    #[test]
    fn test_bool_rec_iota_true_branch() {
        let env = MicroEnv::new();
        let checker = MicroChecker::with_env(&env);
        // cond true 10 20 -> 20 (true selects the true-case minor).
        let e = cond_nat(bool_const(true), lit_nat(10), lit_nat(20));
        assert_eq!(checker.whnf(&e), lit_nat(20));
    }

    #[test]
    fn test_bool_rec_iota_false_branch() {
        let env = MicroEnv::new();
        let checker = MicroChecker::with_env(&env);
        let e = cond_nat(bool_const(false), lit_nat(10), lit_nat(20));
        assert_eq!(checker.whnf(&e), lit_nat(10));
    }

    #[test]
    fn test_bool_and_delta_then_rec_iota() {
        let env = bool_env();
        let checker = MicroChecker::with_env(&env);
        // Bool.and true false -> false, via DELTA(Bool.and) + Bool.rec IOTA.
        let e = app(app(const_("Bool.and"), bool_const(true)), bool_const(false));
        assert_eq!(checker.whnf(&e), bool_const(false));
        // Bool.and true true -> true.
        let e2 = app(app(const_("Bool.and"), bool_const(true)), bool_const(true));
        assert_eq!(checker.whnf(&e2), bool_const(true));
    }

    #[test]
    fn test_bool_not_delta_then_rec_iota() {
        let env = bool_env();
        let checker = MicroChecker::with_env(&env);
        assert_eq!(
            checker.whnf(&app(const_("Bool.not"), bool_const(false))),
            bool_const(true)
        );
        assert_eq!(
            checker.whnf(&app(const_("Bool.not"), bool_const(true))),
            bool_const(false)
        );
    }

    #[test]
    fn test_bool_beq_native_iota() {
        let env = MicroEnv::new();
        let checker = MicroChecker::with_env(&env);
        assert_eq!(
            checker.whnf(&app(
                app(const_("Bool.beq"), bool_const(true)),
                bool_const(true)
            )),
            bool_const(true)
        );
        assert_eq!(
            checker.whnf(&app(
                app(const_("Bool.beq"), bool_const(true)),
                bool_const(false)
            )),
            bool_const(false)
        );
    }

    /// `@Nat.rec (λ _ => Nat) base (λ _ ih => Nat.succ ih) major` = base + major.
    fn add_via_natrec(base: MicroExpr, major: MicroExpr) -> MicroExpr {
        let motive = lam(nat_ty(), nat_ty());
        // minor_succ: λ (_ : Nat) (ih : Nat) => Nat.succ ih
        let minor_succ = lam(nat_ty(), lam(nat_ty(), app(const_("Nat.succ"), bvar(0))));
        MicroExpr::App(
            Arc::new(MicroExpr::App(
                Arc::new(MicroExpr::App(
                    Arc::new(MicroExpr::App(
                        Arc::new(const_("Nat.rec")),
                        Arc::new(motive),
                    )),
                    Arc::new(base),
                )),
                Arc::new(minor_succ),
            )),
            Arc::new(major),
        )
    }

    #[test]
    fn test_nat_rec_iota_recurses() {
        let env = MicroEnv::new();
        let checker = MicroChecker::with_env(&env);
        // 5 + 3 = 8 via genuine Nat.rec recursion on the major premise 3.
        let e = add_via_natrec(lit_nat(5), lit_nat(3));
        assert_eq!(checker.whnf(&e), lit_nat(8));
        // base + 0 = base.
        let e0 = add_via_natrec(lit_nat(5), lit_nat(0));
        assert_eq!(checker.whnf(&e0), lit_nat(5));
    }

    #[test]
    fn test_unmodeled_recursor_stays_stuck_fail_closed() {
        // `List.rec` is NOT in the allowlist -> stuck -> value-eq is Unsupported.
        let env = MicroEnv::new();
        let checker = MicroChecker::with_env(&env);
        let stuck = app(const_("List.rec"), lit_nat(0));
        assert!(matches!(
            checker.check_value_eq_result(&stuck, &lit_nat(0)),
            MicroResult::Unsupported(_)
        ));
    }

    #[test]
    fn test_bool_rec_stuck_on_non_constructor_major() {
        // Major premise is a stuck unknown const, not a Bool ctor -> the
        // recursor must NOT fire; value-eq fails closed (Unsupported).
        let env = MicroEnv::new();
        let checker = MicroChecker::with_env(&env);
        let e = cond_nat(const_("Mystery.flag"), lit_nat(10), lit_nat(20));
        assert!(matches!(
            checker.check_value_eq_result(&e, &lit_nat(20)),
            MicroResult::Unsupported(_)
        ));
    }
}

// ========================================================================
// Property-based tests (proptest)
// ========================================================================

mod proptest_micro {
    use super::*;
    use proptest::prelude::*;

    /// Strategy for generating MicroLevel with bounded depth
    fn arb_level(depth: u32) -> BoxedStrategy<MicroLevel> {
        if depth == 0 {
            Just(MicroLevel::Zero).boxed()
        } else {
            prop_oneof![
                4 => Just(MicroLevel::Zero),
                2 => arb_level(depth - 1).prop_map(MicroLevel::succ),
                1 => (arb_level(depth - 1), arb_level(depth - 1))
                    .prop_map(|(l1, l2)| MicroLevel::max(l1, l2)),
                1 => (arb_level(depth - 1), arb_level(depth - 1))
                    .prop_map(|(l1, l2)| MicroLevel::imax(l1, l2)),
            ]
            .boxed()
        }
    }

    /// Strategy for generating closed MicroExpr (no free variables)
    fn arb_closed_expr(depth: u32) -> BoxedStrategy<MicroExpr> {
        if depth == 0 {
            arb_level(2).prop_map(MicroExpr::Sort).boxed()
        } else {
            prop_oneof![
                    // Sort - most common
                    4 => arb_level(2).prop_map(MicroExpr::Sort),
                    // Lambda - less common
                    1 => (arb_closed_expr(depth - 1), arb_closed_expr(depth - 1))
                        .prop_map(|(ty, body)| MicroExpr::Lam(Arc::new(ty), Arc::new(body))),
                    // Pi - less common
                    1 => (arb_closed_expr(depth - 1), arb_closed_expr(depth - 1))
                        .prop_map(|(ty, body)| MicroExpr::Pi(Arc::new(ty), Arc::new(body))),
                    // App - less common
                    1 => (arb_closed_expr(depth - 1), arb_closed_expr(depth - 1))
                        .prop_map(|(f, a)| MicroExpr::App(Arc::new(f), Arc::new(a))),
                    // Let - important for WHNF testing
                    1 => (arb_closed_expr(depth - 1), arb_closed_expr(depth - 1), arb_closed_expr(depth - 1))
                        .prop_map(|(ty, val, body)| MicroExpr::Let(Arc::new(ty), Arc::new(val), Arc::new(body))),
                    // Lit - natural number literals (#1261)
                    1 => (0u64..1000).prop_map(|n| MicroExpr::Lit(MicroLiteral::nat_u64(n))),
                    // Proj - structure projections (#1261)
                    1 => (0u32..4, arb_closed_expr(depth - 1))
                        .prop_map(|(idx, e)| MicroExpr::Proj(idx, Arc::new(e))),
                ]
                .boxed()
        }
    }

    proptest! {
        #![proptest_config(proptest::test_runner::Config::with_cases(64))]

        /// WHNF is idempotent: whnf(whnf(e)) == whnf(e)
        #[test]
        fn prop_whnf_idempotent(e in arb_closed_expr(2)) {
            let checker = MicroChecker::new();
            let whnf1 = checker.whnf(&e);
            let whnf2 = checker.whnf(&whnf1);
            prop_assert_eq!(whnf1, whnf2, "WHNF should be idempotent");
        }

        /// Definitional equality is reflexive: def_eq(e, e) == true
        #[test]
        fn prop_def_eq_reflexive(e in arb_closed_expr(2)) {
            let checker = MicroChecker::new();
            prop_assert!(checker.def_eq(&e, &e), "def_eq should be reflexive");
        }

        /// Definitional equality is symmetric: def_eq(a, b) == def_eq(b, a)
        #[test]
        fn prop_def_eq_symmetric(
            a in arb_closed_expr(2),
            b in arb_closed_expr(2)
        ) {
            let checker = MicroChecker::new();
            let ab = checker.def_eq(&a, &b);
            let ba = checker.def_eq(&b, &a);
            prop_assert_eq!(ab, ba, "def_eq should be symmetric");
        }

        /// Level equality is reflexive
        #[test]
        fn prop_level_eq_reflexive(l in arb_level(3)) {
            prop_assert!(l.level_eq(&l), "level_eq should be reflexive");
        }

        /// Level equality is symmetric
        #[test]
        fn prop_level_eq_symmetric(l1 in arb_level(3), l2 in arb_level(3)) {
            let eq12 = l1.level_eq(&l2);
            let eq21 = l2.level_eq(&l1);
            prop_assert_eq!(eq12, eq21, "level_eq should be symmetric");
        }

        /// WHNF produces a value that is in WHNF (App head is not Lam, no Let)
        #[test]
        fn prop_whnf_is_normal_form(e in arb_closed_expr(2)) {
            let checker = MicroChecker::new();
            let whnf = checker.whnf(&e);
            fn is_whnf(e: &MicroExpr) -> bool {
                match e {
                    MicroExpr::Let(..) => false,
                    MicroExpr::App(f, _) => {
                        let f_is_lam = matches!(f.as_ref(), MicroExpr::Lam(..));
                        !f_is_lam
                    }
                    _ => true,
                }
            }
            prop_assert!(is_whnf(&whnf), "WHNF result should be in weak head normal form");
        }

        /// Beta reduction: (λx.b) a reduces
        #[test]
        fn prop_beta_reduces(
            arg_ty in arb_closed_expr(1),
            body in arb_closed_expr(1),
            arg in arb_closed_expr(1)
        ) {
            let checker = MicroChecker::new();
            let lam = MicroExpr::Lam(Arc::new(arg_ty), Arc::new(body));
            let app = MicroExpr::App(Arc::new(lam), Arc::new(arg));
            let whnf = checker.whnf(&app);
            // Just verify WHNF terminates and produces valid result (not the original app with lam head)
            let result_is_not_redex = !matches!(
                &whnf,
                MicroExpr::App(f, _) if matches!(f.as_ref(), MicroExpr::Lam(..))
            );
            prop_assert!(result_is_not_redex, "Beta reduction should eliminate redex");
        }

        /// Let reduction: let x := v in e reduces correctly
        #[test]
        fn prop_let_reduces(
            ty in arb_closed_expr(1),
            val in arb_closed_expr(1),
            body in arb_closed_expr(1)
        ) {
            let checker = MicroChecker::new();
            let let_expr = MicroExpr::Let(Arc::new(ty), Arc::new(val), Arc::new(body));
            let whnf = checker.whnf(&let_expr);
            // Verify WHNF eliminates the Let at head position
            let result_is_not_let = !matches!(&whnf, MicroExpr::Let(..));
            prop_assert!(result_is_not_let, "Let reduction should eliminate Let at head");
        }
    }
}

// ========================================================================
// MicroLevel::normalize and is_geq exponential blowup fix (#1946)
// ========================================================================

/// Build a nested Max tree of given depth: max(max(max(..., 0), 0), 0)
fn build_nested_max(depth: u32) -> MicroLevel {
    let mut level = MicroLevel::Zero;
    for _ in 0..depth {
        level = MicroLevel::Max(
            Arc::new(level),
            Arc::new(MicroLevel::Succ(Arc::new(MicroLevel::Zero))),
        );
    }
    level
}

#[test]
fn test_normalize_flattens_nested_max() {
    // max(max(0, 1), max(0, 1)) should normalize to just Succ(Zero)
    let one = MicroLevel::Succ(Arc::new(MicroLevel::Zero));
    let inner = MicroLevel::Max(Arc::new(MicroLevel::Zero), Arc::new(one.clone()));
    let nested = MicroLevel::Max(Arc::new(inner.clone()), Arc::new(inner));
    let normed = nested.normalize();
    // After normalization: flattened, deduped → just Succ(Zero)
    assert_eq!(
        normed, one,
        "normalize should flatten and dedup max(max(0,1), max(0,1)) to 1"
    );
}

#[test]
fn test_normalize_deduplicates_same_base() {
    // max(succ(succ(0)), succ(0)) should normalize to succ(succ(0))
    let one = MicroLevel::Succ(Arc::new(MicroLevel::Zero));
    let two = MicroLevel::Succ(Arc::new(one.clone()));
    let max_level = MicroLevel::Max(Arc::new(two.clone()), Arc::new(one));
    let normed = max_level.normalize();
    assert_eq!(normed, two, "normalize should keep only the larger offset");
}

#[test]
fn test_is_geq_no_exponential_blowup_depth_20() {
    // This is the key test from acceptance criteria:
    // Random nested Max trees of depth 20+ must complete in <1ms
    let tree1 = build_nested_max(25);
    let tree2 = build_nested_max(25);

    let start = std::time::Instant::now();
    let _result = MicroLevel::is_geq(&tree1, &tree2);
    let elapsed = start.elapsed();

    assert!(
        elapsed.as_millis() < 100,
        "is_geq on depth-25 nested Max trees took {}ms, expected <100ms",
        elapsed.as_millis()
    );
}

#[test]
fn test_is_geq_no_exponential_blowup_depth_30() {
    // Even deeper nesting
    let tree1 = build_nested_max(30);
    let tree2 = build_nested_max(30);

    let start = std::time::Instant::now();
    let _result = MicroLevel::is_geq(&tree1, &tree2);
    let elapsed = start.elapsed();

    assert!(
        elapsed.as_millis() < 100,
        "is_geq on depth-30 nested Max trees took {}ms, expected <100ms",
        elapsed.as_millis()
    );
}

#[test]
fn test_is_geq_imax_handling() {
    // l >= imax(a, b) iff l >= a && l >= b
    let one = MicroLevel::Succ(Arc::new(MicroLevel::Zero));
    let two = MicroLevel::Succ(Arc::new(one.clone()));
    let imax = MicroLevel::IMax(Arc::new(MicroLevel::Zero), Arc::new(one.clone()));

    // two >= imax(0, 1) should be true (2 >= 0 && 2 >= 1)
    assert!(MicroLevel::is_geq(&two, &imax), "2 >= imax(0, 1)");

    // zero >= imax(0, 1) should be false (0 >= 1 is false)
    assert!(
        !MicroLevel::is_geq(&MicroLevel::Zero, &imax),
        "0 >= imax(0, 1) is false"
    );
}

#[test]
fn test_is_geq_imax_left() {
    // imax(a, b) >= l iff b >= l
    let one = MicroLevel::Succ(Arc::new(MicroLevel::Zero));
    let two = MicroLevel::Succ(Arc::new(one.clone()));
    let imax = MicroLevel::IMax(Arc::new(MicroLevel::Zero), Arc::new(two.clone()));

    // imax(0, 2) >= 1 should be true (because b=2 >= 1)
    assert!(MicroLevel::is_geq(&imax, &one), "imax(0, 2) >= 1");

    // imax(0, 1) >= 2 should be false (because b=1 >= 2 is false)
    let imax2 = MicroLevel::IMax(Arc::new(MicroLevel::Zero), Arc::new(one.clone()));
    assert!(
        !MicroLevel::is_geq(&imax2, &two),
        "imax(0, 1) >= 2 is false"
    );
}

#[test]
fn test_normalize_preserves_semantics() {
    // Normalization should not change the result of is_geq
    let one = MicroLevel::Succ(Arc::new(MicroLevel::Zero));
    let two = MicroLevel::Succ(Arc::new(one.clone()));
    let three = MicroLevel::Succ(Arc::new(two.clone()));

    // max(max(1, 2), max(0, 3))
    let inner1 = MicroLevel::Max(Arc::new(one.clone()), Arc::new(two.clone()));
    let inner2 = MicroLevel::Max(Arc::new(MicroLevel::Zero), Arc::new(three.clone()));
    let nested = MicroLevel::Max(Arc::new(inner1), Arc::new(inner2));

    let normed = nested.normalize();

    // Both original and normalized should give same is_geq results
    // normed should be 3 (max of all leaves)
    assert!(MicroLevel::is_geq(&normed, &three), "normalized max >= 3");
    assert!(
        MicroLevel::is_geq(&normed, &MicroLevel::Zero),
        "normalized max >= 0"
    );
}

#[test]
fn test_normalize_imax_reduces() {
    // imax(1, succ(0)) should reduce to max(1, 1) = 1
    let one = MicroLevel::Succ(Arc::new(MicroLevel::Zero));
    let imax = MicroLevel::IMax(Arc::new(one.clone()), Arc::new(one.clone()));
    let normed = imax.normalize();
    assert_eq!(normed, one, "imax(1, 1) normalizes to 1");
}

#[test]
fn test_verify_bvar_cross_check_depth_3() {
    // Verify the lift(0, depth-ctx_pos) formula works at depth > 2.
    //
    // Expression: λ (A : Type). λ (f : A → A). λ (x : A). f x
    // At depth 3, BVar(2) refers to A (pushed at depth 0), BVar(1) to f,
    // BVar(0) to x. The types stored in context must be lifted correctly:
    //   - ctx[0] = Type       (pushed at depth 0, lift by 3 to access at depth 3)
    //   - ctx[1] = A → A      = BVar(0)→BVar(0) (pushed at depth 1, lift by 2)
    //   - ctx[2] = A          = BVar(0) (pushed at depth 2, lift by 1)
    //
    // After lifting:
    //   - ctx[0] lifted: Type (no BVars, unchanged)
    //   - ctx[1] lifted: BVar(2)→BVar(2)  (was BVar(0)→BVar(0), lifted by 2)
    //   - ctx[2] lifted: BVar(2)           (was BVar(0), lifted by 1... wait)
    //
    // Actually: ctx_pos for BVar(0)=2, lift=3-2=1 → BVar(0) becomes BVar(1)?
    // No: BVar(0) in ctx[2] was stored at depth 2. At depth 2, BVar(0)
    // refers to the second parameter (f). After lifting by 1, BVar(1)
    // still refers to f at depth 3. But BVar(0) at depth 3 refers to x,
    // and x has type A = the first parameter. A at depth 3 is BVar(2).
    //
    // Let's verify: ctx[2] = BVar(0) (the type of the Lam binder at depth 2).
    // This is the type annotation of the third lambda, which is A.
    // A at depth 2 is BVar(1) (refers to first parameter through 2 binders).
    // Wait — A is the outermost parameter. At depth 2 (inside 2 lambdas),
    // A = BVar(1). So ctx[2] should store BVar(1), not BVar(0).
    //
    // Let's build this step by step and verify the cross-check rejects
    // a forged BVar type at depth 3.
    let mut checker = MicroChecker::new();
    let type1 = sort(l1()); // Type 1

    // λ (A : Type). λ (x : A). λ (y : A). x
    // At depth 0: push A : Type
    // At depth 1: push x : BVar(0)  (A is BVar(0) at depth 1)
    // At depth 2: push y : BVar(1)  (A is BVar(1) at depth 2)
    // Body: BVar(1) (refers to x)
    //
    // For BVar(1) at depth 3:
    //   ctx_pos = 3 - 1 - 1 = 1
    //   ctx[1] = BVar(0)  (stored at depth 1)
    //   lift(0, 3-1=2): BVar(0) → BVar(2)
    //   Certificate must claim BVar(1) has type BVar(2) (= A at depth 3)
    let a_type = bvar(0); // Type of x: A, represented as BVar(0) at depth 1
    let a_at_depth2 = bvar(1); // Type of y: A, represented as BVar(1) at depth 2

    let expr = lam(type1.clone(), lam(a_type, lam(a_at_depth2, bvar(1))));

    // Correct certificate: BVar(1) at depth 3 has type BVar(2) (A lifted to depth 3)
    let correct_cert = MicroCert::Lam {
        arg_ty_cert: Box::new(MicroCert::Sort { level: l1() }),
        body_cert: Box::new(MicroCert::Lam {
            arg_ty_cert: Box::new(MicroCert::BVar {
                idx: 0,
                ty: Box::new(type1.clone()),
            }),
            body_cert: Box::new(MicroCert::Lam {
                arg_ty_cert: Box::new(MicroCert::BVar {
                    idx: 1, // A at depth 2 is BVar(1)
                    ty: Box::new(type1.clone()),
                }),
                body_cert: Box::new(MicroCert::BVar {
                    idx: 1,                // refers to x
                    ty: Box::new(bvar(2)), // A at depth 3 is BVar(2)
                }),
                result_ty: Box::new(pi(bvar(1), bvar(2))),
            }),
            result_ty: Box::new(pi(bvar(0), pi(bvar(1), bvar(2)))),
        }),
        result_ty: Box::new(pi(type1.clone(), pi(bvar(0), pi(bvar(1), bvar(2))))),
    };

    let result = checker.verify(&correct_cert, &expr);
    assert!(
        result.is_ok(),
        "Correct depth-3 BVar types should verify, got: {result:?}"
    );

    // Forged certificate: claims BVar(1) at depth 3 has type BVar(0)
    // instead of BVar(2). The cross-check should reject this.
    let forged_cert = MicroCert::Lam {
        arg_ty_cert: Box::new(MicroCert::Sort { level: l1() }),
        body_cert: Box::new(MicroCert::Lam {
            arg_ty_cert: Box::new(MicroCert::BVar {
                idx: 0,
                ty: Box::new(type1.clone()),
            }),
            body_cert: Box::new(MicroCert::Lam {
                arg_ty_cert: Box::new(MicroCert::BVar {
                    idx: 1,
                    ty: Box::new(type1.clone()),
                }),
                body_cert: Box::new(MicroCert::BVar {
                    idx: 1,
                    ty: Box::new(bvar(0)), // FORGED: should be BVar(2)
                }),
                result_ty: Box::new(pi(bvar(1), bvar(2))),
            }),
            result_ty: Box::new(pi(bvar(0), pi(bvar(1), bvar(2)))),
        }),
        result_ty: Box::new(pi(type1.clone(), pi(bvar(0), pi(bvar(1), bvar(2))))),
    };

    let forged_result = checker.verify(&forged_cert, &expr);
    assert!(
        matches!(forged_result, Err(MicroError::TypeMismatch { .. })),
        "Forged BVar type at depth 3 should be rejected, got: {forged_result:?}"
    );
}

#[test]
fn deep_micro_values_clone_compare_debug_and_drop_on_tiny_stack() {
    crate::test_utils::run_with_stack(256 * 1024, || {
        let mut level = MicroLevel::Zero;
        let mut expr = MicroExpr::BVar(0);
        let mut cert = MicroCert::Sort {
            level: MicroLevel::Zero,
        };
        for idx in 0..20_000 {
            level = MicroLevel::Succ(Arc::new(level));
            expr = MicroExpr::Proj(idx, Arc::new(expr));
            cert = MicroCert::Proj {
                idx,
                expr_cert: Box::new(cert),
                field_ty: Box::new(MicroExpr::BVar(idx)),
            };
        }

        let level_clone = level.clone();
        let expr_clone = expr.clone();
        let cert_clone = cert.clone();
        assert_eq!(level, level_clone);
        assert_eq!(expr, expr_clone);
        assert_eq!(cert, cert_clone);
        assert!(format!("{level:?}").len() < 256);
        assert!(format!("{expr:?}").len() < 256);
        assert!(format!("{cert:?}").len() < 512);

        // All six recursive roots are intentionally dropped normally on this
        // 256 KiB thread.
    });
}

#[test]
fn shallow_micro_debug_is_exact() {
    assert_eq!(
        format!("{:?}", MicroLevel::Succ(Arc::new(MicroLevel::Zero))),
        "Succ(Zero)"
    );
    assert_eq!(
        format!("{:?}", MicroExpr::Proj(3, Arc::new(MicroExpr::BVar(7)))),
        "Proj(3, BVar)"
    );
    assert_eq!(
        format!(
            "{:?}",
            MicroCert::Proj {
                idx: 3,
                expr_cert: Box::new(MicroCert::Sort {
                    level: MicroLevel::Zero,
                }),
                field_ty: Box::new(MicroExpr::BVar(7)),
            }
        ),
        "Proj { idx: 3, expr_cert: Sort, field_ty: BVar }"
    );
}

#[test]
fn huge_nat_debug_is_bounded_and_does_not_materialize_all_digits() {
    crate::test_utils::run_with_stack(256 * 1024, || {
        let huge = (num_bigint::BigUint::from(1_u8) << 1_000_000_usize)
            + num_bigint::BigUint::from(0xfeed_beef_u64);
        let expr = MicroExpr::Lit(MicroLiteral::Nat(huge.clone()));
        let cert = MicroCert::Lit {
            lit: MicroLiteral::Nat(huge),
            ty: Box::new(MicroExpr::BVar(0)),
        };

        let expr_output = format!("{expr:?}");
        let cert_output = format!("{cert:?}");
        assert!(expr_output.contains("bits: 1000001"));
        assert!(expr_output.contains("4276993775"));
        assert!(cert_output.contains("bits: 1000001"));
        assert!(expr_output.len() < 256);
        assert!(cert_output.len() < 512);
    });
}
