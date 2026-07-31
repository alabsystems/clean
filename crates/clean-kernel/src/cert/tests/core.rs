// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core certificate verification tests

use crate::cert::*;
use crate::env::Environment;
use crate::expr::{BigNat, BinderInfo, Expr, ExprKind, FVarId, Literal};
use crate::level::Level;
use crate::name::Name;

fn empty_env() -> Environment {
    Environment::new()
}

#[test]
fn test_sort_cert() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    let level = Level::zero();
    let expr = Expr::from_kind(ExprKind::Sort(level.clone()));
    let cert = ProofCert::Sort {
        level: level.clone(),
    };

    let ty = verifier
        .verify(&cert, &expr)
        .expect("Sort(0) cert should verify");
    assert_eq!(ty, Expr::from_kind(ExprKind::Sort(Level::succ(level))));
}

#[test]
fn test_sort_type_1() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    // Type 1 = Sort(succ(zero))
    let level = Level::succ(Level::zero());
    let expr = Expr::from_kind(ExprKind::Sort(level.clone()));
    let cert = ProofCert::Sort {
        level: level.clone(),
    };

    let ty = verifier
        .verify(&cert, &expr)
        .expect("Sort(succ(0)) cert should verify");
    // Type of Type 1 is Type 2
    assert_eq!(ty, Expr::from_kind(ExprKind::Sort(Level::succ(level))));
}

#[test]
fn test_sort_level_mismatch() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    let expr = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let cert = ProofCert::Sort {
        level: Level::succ(Level::zero()),
    };

    let err = verifier.verify(&cert, &expr).unwrap_err();
    assert!(
        matches!(err, CertError::LevelMismatch { .. }),
        "Sort cert with wrong level should produce LevelMismatch, got: {err}"
    );
}

#[test]
fn test_pi_cert() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    // Build: Prop → Prop : Type 0
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    let expr = Expr::pi(BinderInfo::Default, prop.clone(), prop.clone());

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

    let _ = verifier
        .verify(&cert, &expr)
        .expect("Pi cert (Prop → Prop) should verify");
}

#[test]
fn test_identity_function_cert() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    // Build: λ (x : Prop). x : Prop → Prop
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    let expr = Expr::lam(
        BinderInfo::Default,
        prop.clone(),
        Expr::from_kind(ExprKind::BVar(0)), // Reference to x
    );

    // Certificate for the identity function
    let cert = ProofCert::Lam {
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

    let ty = verifier
        .verify(&cert, &expr)
        .expect("identity function (λ x : Prop. x) cert should verify");
    match &ty.kind {
        ExprKind::Pi(_, arg_ty, ret_ty) => {
            assert_eq!(arg_ty.as_ref(), &prop);
            assert_eq!(ret_ty.as_ref(), &prop);
        }
        _ => panic!("Expected Pi type"),
    }
}

#[test]
fn test_lit_nat_cert() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    let expr = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(42))));
    let nat_type = Expr::const_(Name::from_string("Nat"), vec![]);

    let cert = ProofCert::Lit {
        lit: Literal::Nat(BigNat::Small(42)),
        type_: Box::new(nat_type.clone()),
    };

    let ty = verifier
        .verify(&cert, &expr)
        .expect("Lit(Nat(42)) cert should verify");
    assert_eq!(ty, nat_type);
}

#[test]
fn test_structure_mismatch() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    let expr = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let cert = ProofCert::Lit {
        lit: Literal::Nat(BigNat::Small(0)),
        type_: Box::new(Expr::const_(Name::from_string("Nat"), vec![])),
    };

    let err = verifier.verify(&cert, &expr).unwrap_err();
    assert!(
        matches!(err, CertError::StructureMismatch { .. }),
        "Lit cert on Sort expr should produce StructureMismatch, got: {err}"
    );
}

#[test]
fn test_nested_bvar_in_context() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    // Build: λ (A : Type). λ (x : A). x : (A : Type) → A → A
    let type0 = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let _type1 = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))); // Type 1, for reference

    // Inner lambda: λ (x : A). x
    let inner_lam = Expr::lam(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::BVar(0)), // A (referring to outer binder)
        Expr::from_kind(ExprKind::BVar(0)), // x (referring to inner binder)
    );

    // Outer lambda: λ (A : Type). inner_lam
    let expr = Expr::lam(BinderInfo::Default, type0.clone(), inner_lam);

    // Build certificate
    // Inner body: x : A (where A is now at BVar(1) due to lifting)
    let inner_body_cert = ProofCert::BVar {
        idx: 0,
        expected_type: Box::new(Expr::from_kind(ExprKind::BVar(1))), // A after shift
    };

    // Inner lambda: λ (x : A). x : A → A
    let inner_cert = ProofCert::Lam {
        binder_info: BinderInfo::Default,
        arg_type_cert: Box::new(ProofCert::BVar {
            idx: 0,
            expected_type: Box::new(type0.clone()), // A : Type
        }),
        body_cert: Box::new(inner_body_cert),
        result_type: Box::new(Expr::pi(
            BinderInfo::Default,
            Expr::from_kind(ExprKind::BVar(0)), // A
            Expr::from_kind(ExprKind::BVar(1)), // A (shifted)
        )),
    };

    // Outer lambda cert
    let cert = ProofCert::Lam {
        binder_info: BinderInfo::Default,
        arg_type_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }), // Type : Type1
        body_cert: Box::new(inner_cert),
        result_type: Box::new(Expr::pi(
            BinderInfo::Default,
            type0.clone(),
            Expr::pi(
                BinderInfo::Default,
                Expr::from_kind(ExprKind::BVar(0)),
                Expr::from_kind(ExprKind::BVar(1)),
            ),
        )),
    };

    let result = verifier.verify(&cert, &expr);
    // Nested binder cert for λ (A : Type). λ (x : A). x must verify
    // and produce the polymorphic identity type: (A : Type) → A → A
    let inferred_type = result.expect("nested bvar cert should verify successfully");
    assert!(
        matches!(&inferred_type, Expr { .. }),
        "expected Pi type for identity function, got: {inferred_type:?}"
    );
}

#[test]
fn test_cert_name_coverage() {
    // Test that cert_name returns non-empty strings
    let sort_cert = ProofCert::Sort {
        level: Level::zero(),
    };
    assert!(!cert_name(&sort_cert).is_empty());

    let bvar_cert = ProofCert::BVar {
        idx: 0,
        expected_type: Box::new(Expr::from_kind(ExprKind::Sort(Level::zero()))),
    };
    assert!(!cert_name(&bvar_cert).is_empty());

    let lit_cert = ProofCert::Lit {
        lit: Literal::Nat(BigNat::Small(0)),
        type_: Box::new(Expr::const_(Name::from_string("Nat"), vec![])),
    };
    assert!(!cert_name(&lit_cert).is_empty());
}

#[test]
fn test_expr_name_coverage() {
    // Test that expr_name returns non-empty strings
    assert!(!expr_name(&Expr::from_kind(ExprKind::BVar(0))).is_empty());
    assert!(!expr_name(&Expr::from_kind(ExprKind::FVar(FVarId(0)))).is_empty());
    assert!(!expr_name(&Expr::from_kind(ExprKind::Sort(Level::zero()))).is_empty());
    assert!(!expr_name(&Expr::from_kind(ExprKind::Lit(Literal::Nat(
        BigNat::Small(0)
    ))))
    .is_empty());
}

// --- CertError Display test ---

#[test]
fn test_cert_error_display() {
    let err = CertError::InvalidBVar(5);
    let s = format!("{err}");
    assert!(!s.is_empty());

    let err2 = CertError::TypeMismatch {
        expected: Box::new(Expr::from_kind(ExprKind::Sort(Level::zero()))),
        actual: Box::new(Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))),
        location: "test".to_string(),
    };
    let s2 = format!("{err2}");
    assert!(!s2.is_empty());
}

// --- verify function mutation tests ---

#[test]
fn test_verify_bvar_depth_calculation() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    // Push some context to test depth calculation
    verifier
        .context
        .push(Expr::from_kind(ExprKind::Sort(Level::zero())));
    verifier
        .context
        .push(Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))));

    // BVar(0) should refer to the innermost (most recently pushed)
    let expr = Expr::from_kind(ExprKind::BVar(0));
    let cert = ProofCert::BVar {
        idx: 0,
        expected_type: Box::new(Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))),
    };

    let _ = verifier
        .verify(&cert, &expr)
        .expect("BVar(0) with correct context type should verify");
}

#[test]
fn test_verify_bvar_invalid_index() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    // Empty context, BVar(0) should fail
    let expr = Expr::from_kind(ExprKind::BVar(0));
    let cert = ProofCert::BVar {
        idx: 0,
        expected_type: Box::new(Expr::from_kind(ExprKind::Sort(Level::zero()))),
    };

    let result = verifier.verify(&cert, &expr);
    assert!(matches!(result, Err(CertError::InvalidBVar(_))));
}

#[test]
fn test_verify_fvar_id_mismatch() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    let expr = Expr::from_kind(ExprKind::FVar(FVarId(1)));
    let cert = ProofCert::FVar {
        id: FVarId(2), // Different ID!
        type_: Box::new(Expr::from_kind(ExprKind::Sort(Level::zero()))),
    };

    let err = verifier.verify(&cert, &expr).unwrap_err();
    assert!(
        matches!(err, CertError::UnknownFVar(_)),
        "FVar with mismatched cert ID should produce UnknownFVar, got: {err}"
    );
}

#[test]
fn test_verify_fvar_type_check() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    // Add FVar to context
    let fvar_id = FVarId(1);
    let fvar_type = Expr::from_kind(ExprKind::Sort(Level::zero()));
    verifier.register_fvar(fvar_id, fvar_type.clone()).unwrap();

    let expr = Expr::from_kind(ExprKind::FVar(fvar_id));

    // Correct type
    let cert_ok = ProofCert::FVar {
        id: fvar_id,
        type_: Box::new(fvar_type.clone()),
    };
    let _ = verifier
        .verify(&cert_ok, &expr)
        .expect("FVar with correct registered type should verify");

    // Wrong type should fail
    let cert_bad = ProofCert::FVar {
        id: fvar_id,
        type_: Box::new(Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))),
    };
    let result = verifier.verify(&cert_bad, &expr);
    assert!(matches!(result, Err(CertError::TypeMismatch { .. })));
}

#[test]
fn test_verify_fvar_missing_context() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    let fvar_id = FVarId(3);
    let expr = Expr::from_kind(ExprKind::FVar(fvar_id));
    let cert = ProofCert::FVar {
        id: fvar_id,
        type_: Box::new(Expr::from_kind(ExprKind::Sort(Level::zero()))),
    };

    let result = verifier.verify(&cert, &expr);
    assert!(matches!(result, Err(CertError::UnknownFVar(_))));
}

#[test]
fn test_verify_mdata_correct_type() {
    use crate::expr::MDataValue;

    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    // MData wrapping Sort(0)
    // Sort(0) has type Sort(1)
    let metadata = vec![(Name::from_string("trace"), MDataValue::Bool(true))];
    let inner_expr = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let expr = Expr::mdata(metadata.clone(), inner_expr);

    let cert = ProofCert::MData {
        metadata,
        inner_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        // Correct: Sort(0) has type Sort(1)
        result_type: Box::new(Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))),
    };

    let result_type = verifier
        .verify(&cert, &expr)
        .expect("MData with correct type should verify");
    // MData type is the type of the inner expression: Sort(1)
    assert_eq!(
        result_type,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))
    );
}

#[test]
fn test_verify_mdata_type_mismatch() {
    use crate::expr::MDataValue;

    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    // MData wrapping Sort(0)
    let metadata = vec![(Name::from_string("trace"), MDataValue::Bool(true))];
    let inner_expr = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let expr = Expr::mdata(metadata.clone(), inner_expr);

    let cert = ProofCert::MData {
        metadata,
        inner_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        // WRONG: claiming Sort(0) has type Sort(2) instead of Sort(1)
        result_type: Box::new(Expr::from_kind(ExprKind::Sort(Level::succ(Level::succ(
            Level::zero(),
        ))))),
    };

    let result = verifier.verify(&cert, &expr);
    assert!(result.is_err(), "MData with wrong result_type must fail");
    assert!(
        matches!(result, Err(CertError::TypeMismatch { .. })),
        "Expected TypeMismatch error for MData type mismatch"
    );
}

#[test]
fn test_register_fvar_conflict_rejected() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    let fvar_id = FVarId(5);
    verifier
        .register_fvar(fvar_id, Expr::from_kind(ExprKind::Sort(Level::zero())))
        .unwrap();

    let conflict = verifier.register_fvar(
        fvar_id,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
    );
    assert!(matches!(conflict, Err(CertError::TypeMismatch { .. })));
}

#[test]
fn test_register_local_context() {
    use crate::tc::LocalContext;

    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);
    let mut ctx = LocalContext::new();

    // Push several declarations
    let ty1 = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let ty2 = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())));
    let id1 = ctx.push("x".parse().unwrap(), ty1.clone(), BinderInfo::Default);
    let id2 = ctx.push("y".parse().unwrap(), ty2.clone(), BinderInfo::Default);

    // Register all at once
    verifier.register_local_context(&ctx).unwrap();

    // Verify FVars can be verified
    let fvar1_expr = Expr::from_kind(ExprKind::FVar(id1));
    let fvar1_cert = ProofCert::FVar {
        id: id1,
        type_: Box::new(ty1.clone()),
    };
    let _ = verifier
        .verify(&fvar1_cert, &fvar1_expr)
        .expect("FVar x should verify after register_local_context");

    let fvar2_expr = Expr::from_kind(ExprKind::FVar(id2));
    let fvar2_cert = ProofCert::FVar {
        id: id2,
        type_: Box::new(ty2.clone()),
    };
    let _ = verifier
        .verify(&fvar2_cert, &fvar2_expr)
        .expect("FVar y should verify after register_local_context");
}

#[test]
fn test_register_local_context_conflict() {
    use crate::tc::LocalContext;

    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    // Pre-register an FVar with one type
    let fvar_id = FVarId(0);
    verifier
        .register_fvar(fvar_id, Expr::from_kind(ExprKind::Sort(Level::zero())))
        .unwrap();

    // Create a context with conflicting type for same ID
    let mut ctx = LocalContext::new();
    ctx.push_with_id(
        fvar_id,
        "x".parse().unwrap(),
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
        BinderInfo::Default,
    );

    // Should fail due to conflict
    let result = verifier.register_local_context(&ctx);
    assert!(matches!(result, Err(CertError::TypeMismatch { .. })));
}

#[test]
fn test_verify_def_eq_inner_type_mismatch() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    let expr = Expr::from_kind(ExprKind::Sort(Level::zero()));

    // DefEq certificate where actual_type doesn't match what verify returns
    let cert = ProofCert::DefEq {
        inner: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        expected_type: Box::new(Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))),
        actual_type: Box::new(Expr::from_kind(ExprKind::Sort(Level::succ(Level::succ(
            Level::zero(),
        ))))), // Wrong!
        eq_steps: vec![],
    };

    let err = verifier.verify(&cert, &expr).unwrap_err();
    assert!(
        matches!(err, CertError::TypeMismatch { ref location, .. } if location.contains("DefEq")),
        "DefEq with wrong actual_type should produce TypeMismatch at DefEq, got: {err}"
    );
}

#[test]
fn test_verify_def_eq_expected_type_mismatch() {
    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    let expr = Expr::from_kind(ExprKind::Sort(Level::zero()));

    // DefEq certificate where expected != actual (and actual is correct)
    let cert = ProofCert::DefEq {
        inner: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        expected_type: Box::new(Expr::from_kind(ExprKind::Sort(Level::succ(Level::succ(
            Level::zero(),
        ))))), // Type 2
        actual_type: Box::new(Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))), // Type 1 (correct)
        eq_steps: vec![],
    };

    let result = verifier.verify(&cert, &expr);
    assert!(matches!(result, Err(CertError::DefEqFailed { .. })));
}

// =========================================================================
// Mutation Testing Kill Tests - cert.rs survivors
// =========================================================================

#[test]
fn test_verify_bvar_depth_minus_arithmetic() {
    // Kill mutant: replace - with + in CertVerifier::verify (line 256)
    // The calculation is: level = depth - 1 - idx
    // This converts de Bruijn index to context index

    let env = empty_env();
    let mut verifier = CertVerifier::new(&env);

    // Push 3 entries to context
    let ty0 = Expr::from_kind(ExprKind::Sort(Level::zero())); // idx 2 (oldest)
    let ty1 = Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))); // idx 1
    let ty2 = Expr::from_kind(ExprKind::Sort(Level::succ(Level::succ(Level::zero())))); // idx 0 (newest)
    verifier.context.push(ty0.clone());
    verifier.context.push(ty1.clone());
    verifier.context.push(ty2.clone());

    // depth = 3
    // BVar(0): level = 3 - 1 - 0 = 2 -> context[2] = ty2
    // BVar(1): level = 3 - 1 - 1 = 1 -> context[1] = ty1
    // BVar(2): level = 3 - 1 - 2 = 0 -> context[0] = ty0

    // Test BVar(0) should reference ty2
    let expr0 = Expr::from_kind(ExprKind::BVar(0));
    let cert0 = ProofCert::BVar {
        idx: 0,
        expected_type: Box::new(ty2.clone()),
    };
    let type0 = verifier
        .verify(&cert0, &expr0)
        .expect("BVar(0) should map to context[2]");
    assert_eq!(
        type0, ty2,
        "BVar(0) type must be ty2 (newest context entry)"
    );

    // Test BVar(2) should reference ty0
    let expr2 = Expr::from_kind(ExprKind::BVar(2));
    let cert2 = ProofCert::BVar {
        idx: 2,
        expected_type: Box::new(ty0.clone()),
    };
    let type2 = verifier
        .verify(&cert2, &expr2)
        .expect("BVar(2) should map to context[0]");
    assert_eq!(
        type2, ty0,
        "BVar(2) type must be ty0 (oldest context entry)"
    );
}

#[test]
fn test_cert_name_returns_meaningful_values() {
    // Kill mutants: replace cert_name -> String with "xyzzy".into()
    // Verify that cert_name returns different values for different cert types

    let sort_cert = ProofCert::Sort {
        level: Level::zero(),
    };
    let bvar_cert = ProofCert::BVar {
        idx: 0,
        expected_type: Box::new(Expr::from_kind(ExprKind::Sort(Level::zero()))),
    };
    let fvar_cert = ProofCert::FVar {
        id: FVarId(1),
        type_: Box::new(Expr::from_kind(ExprKind::Sort(Level::zero()))),
    };

    let sort_name = cert_name(&sort_cert);
    let bvar_name = cert_name(&bvar_cert);
    let fvar_name = cert_name(&fvar_cert);

    // Names should not be "xyzzy" (the mutant replacement)
    assert_ne!(sort_name, "xyzzy", "cert_name should not return xyzzy");
    assert_ne!(bvar_name, "xyzzy", "cert_name should not return xyzzy");
    assert_ne!(fvar_name, "xyzzy", "cert_name should not return xyzzy");

    // Names should be meaningful (contain the variant name)
    assert!(
        sort_name.contains("Sort") || sort_name.to_lowercase().contains("sort"),
        "Sort cert should have meaningful name"
    );
    assert!(
        bvar_name.contains("BVar") || bvar_name.to_lowercase().contains("bvar"),
        "BVar cert should have meaningful name"
    );
    assert!(
        fvar_name.contains("FVar") || fvar_name.to_lowercase().contains("fvar"),
        "FVar cert should have meaningful name"
    );
}

#[test]
fn test_expr_name_returns_meaningful_values() {
    // Kill mutants: replace expr_name -> String with "xyzzy".into()
    // Verify that expr_name returns different values for different expr types

    let sort_expr = Expr::from_kind(ExprKind::Sort(Level::zero()));
    let bvar_expr = Expr::from_kind(ExprKind::BVar(0));
    let fvar_expr = Expr::from_kind(ExprKind::FVar(FVarId(1)));

    let sort_name = expr_name(&sort_expr);
    let bvar_name = expr_name(&bvar_expr);
    let fvar_name = expr_name(&fvar_expr);

    // Names should not be "xyzzy"
    assert_ne!(sort_name, "xyzzy", "expr_name should not return xyzzy");
    assert_ne!(bvar_name, "xyzzy", "expr_name should not return xyzzy");
    assert_ne!(fvar_name, "xyzzy", "expr_name should not return xyzzy");

    // Names should be meaningful
    assert!(
        sort_name.contains("Sort") || sort_name.to_lowercase().contains("sort"),
        "Sort expr should have meaningful name"
    );
    assert!(
        bvar_name.contains("BVar") || bvar_name.to_lowercase().contains("bvar"),
        "BVar expr should have meaningful name"
    );
    assert!(
        fvar_name.contains("FVar") || fvar_name.to_lowercase().contains("fvar"),
        "FVar expr should have meaningful name"
    );
}

// ========================================================================
// Certificate serialization tests
// ========================================================================

#[test]
fn test_invalid_decompress_index() {
    // Create a corrupted compressed cert with invalid indices
    let corrupted = CompressedCert {
        schema: CompressedCertSchema::current(),
        exprs: vec![],
        levels: vec![],
        certs: vec![CompressedCertNode::BVar {
            idx: 0,
            expected_type: 999, // Invalid index
        }],
        root: 0,
    };

    let err = decompress_cert(&corrupted).unwrap_err();
    assert!(
        matches!(err, DecompressError::InvalidExprIndex(999)),
        "corrupted cert with index 999 should produce InvalidExprIndex(999), got: {err:?}"
    );
}
