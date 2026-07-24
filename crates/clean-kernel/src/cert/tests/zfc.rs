// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ZFC set theory certificate tests

use crate::cert::*;
use crate::env::{Declaration, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind, FVarId, Literal};
use crate::level::Level;
use crate::mode::CleanMode;
use crate::name::Name;

fn empty_env() -> Environment {
    Environment::new()
}

/// Environment with ZFC.Set declared as an axiom (ZFC.Set : Type 1).
/// Required for tests that use ZFC.Set as a type annotation in lambda/pi expressions.
fn zfc_env() -> Environment {
    let mut env = Environment::with_mode(CleanMode::SetTheoretic);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("ZFC.Set"),
        level_params: vec![],
        type_: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))), // Type 1
    })
    .expect("failed to register ZFC.Set");
    env
}

#[test]
fn test_zfc_empty_set_cert_roundtrip() {
    use crate::expr::ZFCSetExpr;

    let env = empty_env();
    let tc = crate::TypeChecker::with_mode(&env, CleanMode::SetTheoretic);

    let empty_set = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Empty));
    let (ty, cert) = tc.infer_type_with_cert(&empty_set).unwrap();

    let mut verifier = CertVerifier::with_mode(&env, CleanMode::SetTheoretic);
    let verified_ty = verifier.verify(&cert, &empty_set).unwrap();
    assert_eq!(ty, verified_ty);
}

#[test]
fn test_zfc_infinity_set_cert_roundtrip() {
    use crate::expr::ZFCSetExpr;

    let env = empty_env();
    let tc = crate::TypeChecker::with_mode(&env, CleanMode::SetTheoretic);

    let infinity_set = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Infinity));
    let (ty, cert) = tc.infer_type_with_cert(&infinity_set).unwrap();

    let mut verifier = CertVerifier::with_mode(&env, CleanMode::SetTheoretic);
    let verified_ty = verifier.verify(&cert, &infinity_set).unwrap();
    assert_eq!(ty, verified_ty);
}

#[test]
fn test_zfc_singleton_set_cert_roundtrip() {
    use crate::expr::ZFCSetExpr;

    let env = empty_env();
    let tc = crate::TypeChecker::with_mode(&env, CleanMode::SetTheoretic);

    // {∅} - singleton containing empty set
    let empty_set = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Empty));
    let singleton = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Singleton(empty_set.into())));
    let (ty, cert) = tc.infer_type_with_cert(&singleton).unwrap();

    let mut verifier = CertVerifier::with_mode(&env, CleanMode::SetTheoretic);
    let verified_ty = verifier.verify(&cert, &singleton).unwrap();
    assert_eq!(ty, verified_ty);
}

#[test]
fn test_zfc_pair_set_cert_roundtrip() {
    use crate::expr::ZFCSetExpr;

    let env = empty_env();
    let tc = crate::TypeChecker::with_mode(&env, CleanMode::SetTheoretic);

    // {∅, {∅}} - unordered pair
    let empty_set = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Empty));
    let singleton = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Singleton(
        empty_set.clone().into(),
    )));
    let pair = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Pair(
        empty_set.into(),
        singleton.into(),
    )));
    let (ty, cert) = tc.infer_type_with_cert(&pair).unwrap();

    let mut verifier = CertVerifier::with_mode(&env, CleanMode::SetTheoretic);
    let verified_ty = verifier.verify(&cert, &pair).unwrap();
    assert_eq!(ty, verified_ty);
}

#[test]
fn test_zfc_union_set_cert_roundtrip() {
    use crate::expr::ZFCSetExpr;

    let env = empty_env();
    let tc = crate::TypeChecker::with_mode(&env, CleanMode::SetTheoretic);

    // ⋃{{∅}} = {∅}
    let empty_set = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Empty));
    let singleton = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Singleton(empty_set.into())));
    let union = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Union(singleton.into())));
    let (ty, cert) = tc.infer_type_with_cert(&union).unwrap();

    let mut verifier = CertVerifier::with_mode(&env, CleanMode::SetTheoretic);
    let verified_ty = verifier.verify(&cert, &union).unwrap();
    assert_eq!(ty, verified_ty);
}

#[test]
fn test_zfc_powerset_cert_roundtrip() {
    use crate::expr::ZFCSetExpr;

    let env = empty_env();
    let tc = crate::TypeChecker::with_mode(&env, CleanMode::SetTheoretic);

    // P(∅) = {∅}
    let empty_set = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Empty));
    let powerset = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::PowerSet(empty_set.into())));
    let (ty, cert) = tc.infer_type_with_cert(&powerset).unwrap();

    let mut verifier = CertVerifier::with_mode(&env, CleanMode::SetTheoretic);
    let verified_ty = verifier.verify(&cert, &powerset).unwrap();
    assert_eq!(ty, verified_ty);
}

#[test]
fn test_zfc_mem_cert_roundtrip() {
    use crate::expr::ZFCSetExpr;

    let env = empty_env();
    let tc = crate::TypeChecker::with_mode(&env, CleanMode::SetTheoretic);

    // ∅ ∈ {∅}
    let empty_set = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Empty));
    let singleton = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Singleton(
        empty_set.clone().into(),
    )));
    let mem_expr = Expr::from_kind(ExprKind::ZFCMem {
        element: empty_set.into(),
        set: singleton.into(),
    });
    let (ty, cert) = tc.infer_type_with_cert(&mem_expr).unwrap();

    let mut verifier = CertVerifier::with_mode(&env, CleanMode::SetTheoretic);
    let verified_ty = verifier.verify(&cert, &mem_expr).unwrap();
    assert_eq!(ty, verified_ty);
    // Membership is a proposition (Prop = Sort(0))
    assert_eq!(ty, Expr::from_kind(ExprKind::Sort(Level::zero())));
}

#[test]
fn test_zfc_comprehension_cert_roundtrip() {
    use crate::expr::ZFCSetExpr;
    use std::sync::Arc;

    let env = zfc_env();
    let tc = crate::TypeChecker::with_mode(&env, CleanMode::SetTheoretic);

    // {x ∈ ∅ | x ∈ ∅} (comprehension with membership predicate)
    // Predicate must be Set -> Prop
    let empty_set = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Empty));
    let set_ty = Expr::const_(Name::from_string("ZFC.Set"), vec![]);
    let pred = Expr::lam(
        BinderInfo::Default,
        set_ty,
        Expr::from_kind(ExprKind::ZFCMem {
            element: Arc::new(Expr::from_kind(ExprKind::BVar(0))),
            set: Arc::new(Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Empty))),
        }),
    );
    let comprehension = Expr::from_kind(ExprKind::ZFCComprehension {
        domain: empty_set.into(),
        pred: pred.into(),
    });
    let (ty, cert) = tc.infer_type_with_cert(&comprehension).unwrap();

    let mut verifier = CertVerifier::with_mode(&env, CleanMode::SetTheoretic);
    let verified_ty = verifier.verify(&cert, &comprehension).unwrap();
    assert_eq!(ty, verified_ty);
}

#[test]
fn test_zfc_mode_required() {
    use crate::expr::ZFCSetExpr;

    let env = empty_env();
    let tc = crate::TypeChecker::new(&env); // Constructive mode

    let empty_set = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Empty));

    // Should fail in constructive mode
    let result = tc.infer_type_with_cert(&empty_set);
    assert!(
        matches!(result, Err(crate::TypeError::ModeRequired { .. })),
        "expected ModeRequired error in constructive mode, got: {result:?}"
    );
}

#[test]
fn test_zfc_nested_sets_cert_roundtrip() {
    use crate::expr::ZFCSetExpr;

    let env = empty_env();
    let tc = crate::TypeChecker::with_mode(&env, CleanMode::SetTheoretic);

    // P(P(∅)) - power set of power set of empty set
    let empty = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Empty));
    let p1 = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::PowerSet(empty.into())));
    let p2 = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::PowerSet(p1.into())));
    let (ty, cert) = tc.infer_type_with_cert(&p2).unwrap();

    let mut verifier = CertVerifier::with_mode(&env, CleanMode::SetTheoretic);
    let verified_ty = verifier.verify(&cert, &p2).unwrap();
    assert_eq!(ty, verified_ty);
}

// ============================================================================
// ADVERSARIAL TESTS
// ============================================================================

/// Part of #2064: ZFC verifier must independently derive result types, not trust
/// the certificate. A forged cert with result_type=Nat (instead of ZFC.Set) must
/// still return ZFC.Set from the verifier.
/// Regression test for W1-1289 type-trust gap fix.
#[test]
fn test_zfc_set_forged_result_type_ignored() {
    use crate::expr::ZFCSetExpr;

    let env = empty_env();
    let empty_set = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Empty));

    // Forge a cert with result_type = Nat (wrong — should be ZFC.Set)
    let forged_cert = ProofCert::ZFCSet {
        kind: ZFCSetCertKind::Empty,
        result_type: Box::new(Expr::const_(Name::from_string("Nat"), vec![])),
    };

    let mut verifier = CertVerifier::with_mode(&env, CleanMode::SetTheoretic);
    let verified_ty = verifier.verify(&forged_cert, &empty_set).unwrap();

    // Verifier must return ZFC.Set regardless of what the cert claims
    let expected = Expr::const_(Name::from_string("ZFC.Set"), vec![]);
    assert_eq!(
        verified_ty, expected,
        "verifier must independently derive ZFC.Set, not trust cert's result_type"
    );
}

/// Part of #2064: Same test for Infinity set kind — verifier must ignore forged
/// result_type and return ZFC.Set independently.
#[test]
fn test_zfc_infinity_forged_result_type_ignored() {
    use crate::expr::ZFCSetExpr;

    let env = empty_env();
    let infinity = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Infinity));

    // Forge a cert with result_type = Prop (wrong — should be ZFC.Set)
    let forged_cert = ProofCert::ZFCSet {
        kind: ZFCSetCertKind::Infinity,
        result_type: Box::new(Expr::sort(Level::zero())), // Sort(0) = Prop
    };

    let mut verifier = CertVerifier::with_mode(&env, CleanMode::SetTheoretic);
    let verified_ty = verifier.verify(&forged_cert, &infinity).unwrap();

    let expected = Expr::const_(Name::from_string("ZFC.Set"), vec![]);
    assert_eq!(
        verified_ty, expected,
        "verifier must independently derive ZFC.Set for Infinity, not trust cert"
    );
}

/// Part of #2196: Comprehension predicate must be Set -> Prop.
/// A predicate with wrong type (Prop -> Type 1) must be rejected.
#[test]
fn test_zfc_comprehension_wrong_pred_type_rejected() {
    use crate::expr::ZFCSetExpr;

    let env = empty_env();
    let tc = crate::TypeChecker::with_mode(&env, CleanMode::SetTheoretic);

    // Wrong predicate: λ (x : Prop). Prop — has type Prop -> Type 1, not Set -> Prop
    let empty_set = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Empty));
    let prop_ty = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let wrong_pred = Expr::lam(
        BinderInfo::Default,
        prop_ty,
        Expr::from_kind(ExprKind::Sort(Level::zero())),
    );
    let comprehension = Expr::from_kind(ExprKind::ZFCComprehension {
        domain: empty_set.into(),
        pred: wrong_pred.into(),
    });
    let result = tc.infer_type_with_cert(&comprehension);
    assert!(
        matches!(result, Err(crate::TypeError::TypeMismatch { .. })),
        "comprehension with wrong pred type must be rejected, got: {result:?}"
    );
}

/// Part of #2196: Separation predicate must be Set -> Prop.
/// A predicate with wrong type (Nat -> Bool) must be rejected.
#[test]
fn test_zfc_separation_wrong_pred_type_rejected() {
    use crate::expr::ZFCSetExpr;

    let env = empty_env();
    let tc = crate::TypeChecker::with_mode(&env, CleanMode::SetTheoretic);

    // Build Separation { set: ∅, pred: λ (x : Prop). Prop }
    // pred has type Prop -> Type 1, not Set -> Prop
    let empty_set = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Empty));
    let prop_ty = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let wrong_pred = Expr::lam(
        BinderInfo::Default,
        prop_ty,
        Expr::from_kind(ExprKind::Sort(Level::zero())),
    );
    let separation = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Separation {
        set: empty_set.into(),
        pred: wrong_pred.into(),
    }));
    let result = tc.infer_type_with_cert(&separation);
    assert!(
        matches!(result, Err(crate::TypeError::TypeMismatch { .. })),
        "separation with wrong pred type must be rejected, got: {result:?}"
    );
}

/// Part of #2196: Replacement function must be Set -> Set.
/// A function with wrong type (Prop -> Type 1) must be rejected.
#[test]
fn test_zfc_replacement_wrong_func_type_rejected() {
    use crate::expr::ZFCSetExpr;

    let env = empty_env();
    let tc = crate::TypeChecker::with_mode(&env, CleanMode::SetTheoretic);

    // Build Replacement { set: ∅, func: λ (x : Prop). Prop }
    // func has type Prop -> Type 1, not Set -> Set
    let empty_set = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Empty));
    let prop_ty = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let wrong_func = Expr::lam(
        BinderInfo::Default,
        prop_ty,
        Expr::from_kind(ExprKind::Sort(Level::zero())),
    );
    let replacement = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Replacement {
        set: empty_set.into(),
        func: wrong_func.into(),
    }));
    let result = tc.infer_type_with_cert(&replacement);
    assert!(
        matches!(result, Err(crate::TypeError::TypeMismatch { .. })),
        "replacement with wrong func type must be rejected, got: {result:?}"
    );
}

/// Part of #2196: Separation with correctly typed predicate (Set -> Prop) must pass.
#[test]
fn test_zfc_separation_correct_pred_roundtrip() {
    use crate::expr::ZFCSetExpr;
    use std::sync::Arc;

    let env = zfc_env();
    let tc = crate::TypeChecker::with_mode(&env, CleanMode::SetTheoretic);

    // pred: λ (x : ZFC.Set). x ∈ ∅ — has type Set -> Prop
    let set_ty = Expr::const_(Name::from_string("ZFC.Set"), vec![]);
    let pred = Expr::lam(
        BinderInfo::Default,
        set_ty,
        Expr::from_kind(ExprKind::ZFCMem {
            element: Arc::new(Expr::from_kind(ExprKind::BVar(0))),
            set: Arc::new(Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Empty))),
        }),
    );
    let separation = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Separation {
        set: Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Empty)).into(),
        pred: pred.into(),
    }));
    let (ty, cert) = tc.infer_type_with_cert(&separation).unwrap();

    let mut verifier = CertVerifier::with_mode(&env, CleanMode::SetTheoretic);
    let verified_ty = verifier.verify(&cert, &separation).unwrap();
    assert_eq!(ty, verified_ty);
}

/// Part of #2196: Replacement with correctly typed function (Set -> Set) must pass.
#[test]
fn test_zfc_replacement_correct_func_roundtrip() {
    use crate::expr::ZFCSetExpr;

    let env = zfc_env();
    let tc = crate::TypeChecker::with_mode(&env, CleanMode::SetTheoretic);

    // func: λ (x : ZFC.Set). ∅ — has type Set -> Set
    let set_ty = Expr::const_(Name::from_string("ZFC.Set"), vec![]);
    let func = Expr::lam(
        BinderInfo::Default,
        set_ty,
        Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Empty)),
    );
    let replacement = Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Replacement {
        set: Expr::from_kind(ExprKind::ZFCSet(ZFCSetExpr::Empty)).into(),
        func: func.into(),
    }));
    let (ty, cert) = tc.infer_type_with_cert(&replacement).unwrap();

    let mut verifier = CertVerifier::with_mode(&env, CleanMode::SetTheoretic);
    let verified_ty = verifier.verify(&cert, &replacement).unwrap();
    assert_eq!(ty, verified_ty);
}

// ============================================================================
// PROPERTY-BASED TESTS
// ============================================================================

mod proptest_soundness {
    use super::*;
    use proptest::prelude::*;

    /// Strategy for generating Level with bounded depth
    fn arb_level(depth: u32) -> BoxedStrategy<Level> {
        if depth == 0 {
            Just(Level::zero()).boxed()
        } else {
            prop_oneof![
                5 => Just(Level::zero()),
                3 => arb_level(depth - 1).prop_map(Level::succ),
                1 => (arb_level(depth - 1), arb_level(depth - 1))
                    .prop_map(|(l1, l2)| Level::max(l1, l2)),
                1 => (arb_level(depth - 1), arb_level(depth - 1))
                    .prop_map(|(l1, l2)| Level::imax(l1, l2)),
            ]
            .boxed()
        }
    }

    /// Strategy for generating closed Expr (no free variables, well-formed)
    /// Uses a context depth to track available bound variables
    fn arb_closed_expr(depth: u32, ctx_depth: u32) -> BoxedStrategy<Expr> {
        if depth == 0 {
            // Base cases only
            prop_oneof![
                // Sort - always valid
                5 => arb_level(2).prop_map(|l| Expr::from_kind(ExprKind::Sort(l))),
                // BVar - only if we have context
                if ctx_depth > 0 { 2 } else { 0 } => {
                    (0..ctx_depth).prop_map(|i| Expr::from_kind(ExprKind::BVar(i)))
                },
                // Literal Nat - always valid
                2 => (0..100u64).prop_map(Expr::nat_lit),
            ]
            .boxed()
        } else {
            prop_oneof![
                // Sort - most common
                5 => arb_level(2).prop_map(|l| Expr::from_kind(ExprKind::Sort(l))),
                // BVar - only if we have context
                if ctx_depth > 0 { 2 } else { 0 } => {
                    (0..ctx_depth).prop_map(|i| Expr::from_kind(ExprKind::BVar(i)))
                },
                // Lambda - extends context for body
                2 => (arb_closed_expr(depth - 1, ctx_depth), arb_closed_expr(depth - 1, ctx_depth + 1))
                    .prop_map(|(ty, body)| Expr::from_kind(ExprKind::Lam(BinderInfo::Default.into(), ty.into(), body.into()))),
                // Pi - extends context for codomain
                2 => (arb_closed_expr(depth - 1, ctx_depth), arb_closed_expr(depth - 1, ctx_depth + 1))
                    .prop_map(|(ty, body)| Expr::from_kind(ExprKind::Pi(BinderInfo::Default.into(), ty.into(), body.into()))),
                // App - both parts in same context
                2 => (arb_closed_expr(depth - 1, ctx_depth), arb_closed_expr(depth - 1, ctx_depth))
                    .prop_map(|(f, a)| Expr::from_kind(ExprKind::App(f.into(), a.into()))),
                // Let - type and value in current context, body in extended
                1 => (
                    arb_closed_expr(depth - 1, ctx_depth),
                    arb_closed_expr(depth - 1, ctx_depth),
                    arb_closed_expr(depth - 1, ctx_depth + 1)
                )
                    .prop_map(|(ty, val, body)| Expr::from_kind(ExprKind::Let(Name::anon(), ty.into(), val.into(), body.into(), false))),
                // Literal Nat
                1 => (0..1000u64).prop_map(Expr::nat_lit),
            ]
            .boxed()
        }
    }

    /// Strategy for generating well-typed expressions that we can build certificates for.
    /// These are expressions where we know type inference will succeed.
    fn arb_welltyped_expr() -> BoxedStrategy<Expr> {
        prop_oneof![
            // Sort expressions - always well-typed
            5 => arb_level(2).prop_map(|l| Expr::from_kind(ExprKind::Sort(l))),
            // Nat literals - always well-typed
            3 => (0..1000u64).prop_map(Expr::nat_lit),
            // String literals - always well-typed
            1 => "[a-z]{1,10}".prop_map(|s| Expr::from_kind(ExprKind::Lit(Literal::String(s.into())))),
            // Identity function on Prop: λ (x : Prop). x
            2 => Just(Expr::lam(
                BinderInfo::Default,
                Expr::from_kind(ExprKind::Sort(Level::zero())),
                Expr::from_kind(ExprKind::BVar(0)),
            )),
            // Type-level identity: λ (A : Type). A
            2 => Just(Expr::lam(
                BinderInfo::Default,
                Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
                Expr::from_kind(ExprKind::BVar(0)),
            )),
            // Prop → Prop type
            2 => Just(Expr::pi(
                BinderInfo::Default,
                Expr::from_kind(ExprKind::Sort(Level::zero())),
                Expr::from_kind(ExprKind::Sort(Level::zero())),
            )),
            // Polymorphic identity type: (A : Type) → A → A
            1 => Just(Expr::pi(
                BinderInfo::Default,
                Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))), // A : Type
                Expr::pi(
                    BinderInfo::Default,
                    Expr::from_kind(ExprKind::BVar(0)), // x : A
                    Expr::from_kind(ExprKind::BVar(1)), // result: A
                ),
            )),
        ]
        .boxed()
    }

    proptest! {
        #![proptest_config(proptest::test_runner::Config::with_cases(64))]

        /// Soundness: If TypeChecker.infer_type_with_cert succeeds,
        /// then CertVerifier.verify on the same (cert, expr) pair succeeds
        /// and returns the same type.
        #[test]
        fn prop_verify_agrees_with_tc(expr in arb_welltyped_expr()) {
            let env = empty_env();
            let tc = crate::TypeChecker::new(&env);

            // Try type inference with certificate
            match tc.infer_type_with_cert(&expr) {
                Ok((tc_ty, cert)) => {
                    // Verify should succeed and return the same type
                    let mut verifier = CertVerifier::new(&env);
                    let verified_ty = verifier.verify(&cert, &expr);

                    prop_assert!(
                        verified_ty.is_ok(),
                        "If TC succeeds, verifier should succeed. TC type: {:?}, error: {:?}",
                        tc_ty,
                        verified_ty.err()
                    );

                    let verified_ty = verified_ty.unwrap();
                    prop_assert_eq!(
                        tc_ty, verified_ty,
                        "Verified type should match TC type"
                    );
                }
                Err(e) => {
                    // TC failure is acceptable for generated exprs, but must be a TypeError
                    let msg = format!("{e:?}");
                    prop_assert!(!msg.is_empty(), "TypeError should have debug output");
                }
            }
        }

        /// Determinism: Same (cert, expr) pair always produces same result
        #[test]
        fn prop_verify_deterministic(expr in arb_welltyped_expr()) {
            let env = empty_env();
            let tc = crate::TypeChecker::new(&env);

            match tc.infer_type_with_cert(&expr) {
                Ok((_, cert)) => {
                    let mut v1 = CertVerifier::new(&env);
                    let mut v2 = CertVerifier::new(&env);

                    let r1 = v1.verify(&cert, &expr);
                    let r2 = v2.verify(&cert, &expr);

                    match (&r1, &r2) {
                        (Ok(t1), Ok(t2)) => {
                            prop_assert_eq!(t1, t2, "Same cert/expr should produce same type");
                        }
                        (Err(_), Err(_)) => {
                            // Both failed consistently — acceptable
                        }
                        _ => {
                            prop_assert!(false, "Results should be consistent: {:?} vs {:?}", r1, r2);
                        }
                    }
                }
                Err(e) => {
                    // TC failure is acceptable for generated exprs, but must be a TypeError
                    let msg = format!("{e:?}");
                    prop_assert!(!msg.is_empty(), "TypeError should have debug output");
                }
            }
        }

        /// Level equality is reflexive
        #[test]
        fn prop_level_eq_reflexive(l in arb_level(3)) {
            let env = empty_env();
            let verifier = CertVerifier::new(&env);
            // Use the verifier's level_eq method indirectly via def_eq on Sort
            let sort_l = Expr::from_kind(ExprKind::Sort(l.clone()));
            prop_assert!(
                verifier.def_eq(&sort_l, &sort_l),
                "Sort level should be def_eq to itself"
            );
        }

        /// def_eq is reflexive
        #[test]
        fn prop_def_eq_reflexive(e in arb_closed_expr(2, 0)) {
            let env = empty_env();
            let verifier = CertVerifier::new(&env);
            prop_assert!(
                verifier.def_eq(&e, &e),
                "Expression should be def_eq to itself: {:?}",
                e
            );
        }

        /// def_eq is symmetric
        #[test]
        fn prop_def_eq_symmetric(
            a in arb_closed_expr(2, 0),
            b in arb_closed_expr(2, 0)
        ) {
            let env = empty_env();
            let verifier = CertVerifier::new(&env);
            let ab = verifier.def_eq(&a, &b);
            let ba = verifier.def_eq(&b, &a);
            prop_assert_eq!(ab, ba, "def_eq should be symmetric");
        }

        /// def_eq is transitive (if a ≡ b and b ≡ c then a ≡ c)
        #[test]
        fn prop_def_eq_transitive(
            a in arb_closed_expr(2, 0),
            b in arb_closed_expr(2, 0),
            c in arb_closed_expr(2, 0)
        ) {
            let env = empty_env();
            let verifier = CertVerifier::new(&env);
            let ab = verifier.def_eq(&a, &b);
            let bc = verifier.def_eq(&b, &c);
            let ac = verifier.def_eq(&a, &c);
            // If a ≡ b and b ≡ c, then a ≡ c must hold
            if ab && bc {
                prop_assert!(ac, "def_eq should be transitive: a≡b and b≡c but not a≡c");
            }
        }

        /// WHNF is idempotent: whnf(whnf(e)) == whnf(e)
        #[test]
        fn prop_whnf_idempotent(e in arb_closed_expr(2, 0)) {
            let env = empty_env();
            let verifier = CertVerifier::new(&env);
            let whnf1 = verifier.whnf(&e);
            let whnf2 = verifier.whnf(&whnf1);
            // Use structural equality since we're testing WHNF
            prop_assert!(
                verifier.def_eq(&whnf1, &whnf2),
                "WHNF should be idempotent: whnf({:?}) = {:?}, whnf({:?}) = {:?}",
                e, whnf1, whnf1, whnf2
            );
        }

        /// Sort certificate verification is correct for any level
        #[test]
        fn prop_sort_cert_any_level(l in arb_level(3)) {
            let env = empty_env();
            let mut verifier = CertVerifier::new(&env);

            let expr = Expr::from_kind(ExprKind::Sort(l.clone()));
            let cert = ProofCert::Sort { level: l.clone() };

            let result = verifier.verify(&cert, &expr);
            prop_assert!(result.is_ok(), "Sort cert should verify: {:?}", result.err());

            let ty = result.unwrap();
            let expected_ty = Expr::from_kind(ExprKind::Sort(Level::succ(l)));
            prop_assert_eq!(ty, expected_ty, "Sort type should be Sort(succ(level))");
        }

        /// Nat literal certificate verification
        #[test]
        fn prop_nat_lit_cert(n in 0..10000u64) {
            let env = empty_env();
            let mut verifier = CertVerifier::new(&env);

            let expr = Expr::nat_lit(n);
            let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);
            let cert = ProofCert::Lit {
                lit: Literal::nat(n),
                type_: Box::new(nat_type.clone()),
            };

            let result = verifier.verify(&cert, &expr);
            prop_assert!(result.is_ok(), "Nat lit cert should verify: {:?}", result.err());
            prop_assert_eq!(result.unwrap(), nat_type);
        }

        /// String literal certificate verification
        #[test]
        fn prop_string_lit_cert(s in "[a-z]{1,20}") {
            let env = empty_env();
            let mut verifier = CertVerifier::new(&env);

            let expr = Expr::from_kind(ExprKind::Lit(Literal::String(s.clone().into())));
            let string_type = Expr::const_(Name::from_string("String"), vec![]);
            let cert = ProofCert::Lit {
                lit: Literal::String(s.into()),
                type_: Box::new(string_type.clone()),
            };

            let result = verifier.verify(&cert, &expr);
            prop_assert!(result.is_ok(), "String lit cert should verify: {:?}", result.err());
            prop_assert_eq!(result.unwrap(), string_type);
        }

        /// Pi certificate with any valid levels
        #[test]
        fn prop_pi_cert_levels(l1 in arb_level(2), l2 in arb_level(2)) {
            let env = empty_env();
            let mut verifier = CertVerifier::new(&env);

            // Build: Sort(l1) → Sort(l2) : Sort(imax(succ(l1), succ(l2)))
            let arg_sort = Expr::from_kind(ExprKind::Sort(l1.clone()));
            let body_sort = Expr::from_kind(ExprKind::Sort(l2.clone()));

            let expr = Expr::pi(
                BinderInfo::Default,
                arg_sort.clone(),
                body_sort.clone(),
            );

            // Cert: arg is Sort(l1), so arg has type Sort(succ(l1))
            // Body is Sort(l2), so body has type Sort(succ(l2))
            let cert = ProofCert::Pi {
                binder_info: BinderInfo::Default,
                arg_type_cert: Box::new(ProofCert::Sort { level: l1.clone() }),
                arg_level: Level::succ(l1.clone()),
                body_type_cert: Box::new(ProofCert::Sort { level: l2.clone() }),
                body_level: Level::succ(l2.clone()),
            };

            let result = verifier.verify(&cert, &expr);
            prop_assert!(result.is_ok(), "Pi cert should verify: {:?}", result.err());

            // Result should be Sort(imax(succ(l1), succ(l2)))
            let expected = Expr::from_kind(ExprKind::Sort(Level::imax(Level::succ(l1), Level::succ(l2))));
            prop_assert_eq!(result.unwrap(), expected);
        }

        /// Lambda certificate verification for identity functions
        #[test]
        fn prop_lam_identity_cert(l in arb_level(2)) {
            let env = empty_env();
            let mut verifier = CertVerifier::new(&env);

            // Build: λ (x : Sort(l)). x : (x : Sort(l)) → Sort(l)
            let arg_ty = Expr::from_kind(ExprKind::Sort(l.clone()));
            let expr = Expr::lam(
                BinderInfo::Default,
                arg_ty.clone(),
                Expr::from_kind(ExprKind::BVar(0)),
            );

            // Certificate for identity on Sort(l)
            let cert = ProofCert::Lam {
                binder_info: BinderInfo::Default,
                arg_type_cert: Box::new(ProofCert::Sort { level: l.clone() }),
                body_cert: Box::new(ProofCert::BVar {
                    idx: 0,
                    expected_type: Box::new(arg_ty.clone()),
                }),
                result_type: Box::new(Expr::pi(
                    BinderInfo::Default,
                    arg_ty.clone(),
                    arg_ty.clone(),
                )),
            };

            let result = verifier.verify(&cert, &expr);
            prop_assert!(result.is_ok(), "Lam cert should verify: {:?}", result.err());

            // Result should be Pi type
            let ty = result.unwrap();
            let expected_ty = Expr::pi(
                BinderInfo::Default,
                arg_ty.clone(),
                arg_ty,
            );
            prop_assert_eq!(ty, expected_ty);
        }

        /// Let certificate verification
        /// let x : Sort(succ(l)) := Sort(l) in x
        /// The value Sort(l) has type Sort(succ(l)), matching the declared type.
        #[test]
        fn prop_let_cert(l in arb_level(2)) {
            let env = empty_env();
            let mut verifier = CertVerifier::new(&env);

            // Sort(l) has type Sort(succ(l))
            // So: let x : Sort(succ(l)) := Sort(l) in x
            let sort_l = Expr::from_kind(ExprKind::Sort(l.clone()));
            let sort_succ_l = Expr::from_kind(ExprKind::Sort(Level::succ(l.clone())));
            let expr = Expr::let_named(Name::anon(),
                sort_succ_l.clone(), // declared type: Sort(succ(l))
                sort_l.clone(),      // value: Sort(l) which has type Sort(succ(l))
                Expr::from_kind(ExprKind::BVar(0)),       // body: x
                false,
            );

            // Certificate
            let cert = ProofCert::Let {
                type_cert: Box::new(ProofCert::Sort { level: Level::succ(l.clone()) }),
                value_cert: Box::new(ProofCert::Sort { level: l.clone() }),
                body_cert: Box::new(ProofCert::BVar {
                    idx: 0,
                    expected_type: Box::new(sort_succ_l.clone()),
                }),
                result_type: Box::new(sort_succ_l.clone()),
            };

            let result = verifier.verify(&cert, &expr);
            prop_assert!(result.is_ok(), "Let cert should verify: {:?}", result.err());
            prop_assert_eq!(result.unwrap(), sort_succ_l);
        }
    }

    // Additional non-proptest tests for edge cases

    #[test]
    fn test_mismatched_cert_expr_structure() {
        let env = empty_env();
        let mut verifier = CertVerifier::new(&env);

        // Cert for Sort, but Expr is Lit
        let cert = ProofCert::Sort {
            level: Level::zero(),
        };
        let expr = Expr::nat_lit(42);

        let result = verifier.verify(&cert, &expr);
        assert!(
            matches!(result, Err(CertError::StructureMismatch { .. })),
            "expected StructureMismatch, got: {result:?}"
        );
    }

    #[test]
    fn test_invalid_bvar_index() {
        let env = empty_env();
        let mut verifier = CertVerifier::new(&env);

        // BVar(5) but empty context
        let cert = ProofCert::BVar {
            idx: 5,
            expected_type: Box::new(Expr::from_kind(ExprKind::Sort(Level::zero()))),
        };
        let expr = Expr::from_kind(ExprKind::BVar(5));

        let result = verifier.verify(&cert, &expr);
        assert!(
            matches!(result, Err(CertError::InvalidBVar(5))),
            "expected InvalidBVar(5), got: {result:?}"
        );
    }

    #[test]
    fn test_context_consistency_fvar() {
        let env = empty_env();
        let mut verifier = CertVerifier::new(&env);

        let fvar_id = FVarId(42);
        let ty1 = Expr::from_kind(ExprKind::Sort(Level::zero()));
        let ty2 = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));

        // Register with ty1
        verifier.register_fvar(fvar_id, ty1.clone()).unwrap();

        // Re-register with same type should succeed
        verifier
            .register_fvar(fvar_id, ty1.clone())
            .expect("re-registering fvar with same type should succeed");

        // Re-register with different type should fail
        let result = verifier.register_fvar(fvar_id, ty2);
        assert!(
            matches!(result, Err(CertError::TypeMismatch { .. })),
            "expected TypeMismatch, got: {result:?}"
        );
    }
}
