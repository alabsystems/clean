// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `verify_proof` regressions for linarith proof terms.

use super::*;
use crate::tactic::core::TacticError;

/// Coverage gap: verify_proof with typeclass projection types.
///
/// All existing verify_proof tests use trivial types (axiom A, B) where
/// type checking is trivial. This test uses realistic typeclass types
/// (@LE.le Nat instLENat) to verify that verify_proof's WHNF normalization
/// and certified type checking handle projection-heavy types correctly.
///
/// Re: #2150, Re: #2153.
#[test]
fn test_verify_proof_with_typeclass_projection_types() {
    let env = Environment::with_prelude();
    let h_id = FVarId::new(0);
    let h_ty = make_nat_le_tc(Expr::nat_lit(0), Expr::nat_lit(1));
    let target = make_nat_le_tc(Expr::nat_lit(0), Expr::nat_lit(1));
    let state = ProofState::with_context(
        env,
        target,
        vec![LocalDecl {
            fvar: h_id,
            name: "h".into(),
            ty: h_ty,
            value: None,
        }],
    );
    let goal = state.current_goal().expect("should have a goal");

    let proof = Expr::fvar(h_id);
    let cert = state.verify_proof(goal, &proof);
    assert!(
        cert.is_ok(),
        "verify_proof should accept FVar proof with typeclass projection type, got: {cert:?}"
    );
}

/// Previously-documented coverage gap (now CLOSED): CertVerifier could not
/// handle typeclass projection types in linarith proofs.
///
/// The linarith proof's inferred type contains @LE.le Nat instLENat projections.
/// `verify_proof` WHNF-normalizes the inferred type (core.rs:474) and is_def_eq
/// accepts it. The verification path under a `Pi`/`Lam` binder now opens the
/// binder with a fresh local FVar before comparing bodies (see
/// `unify_expr.rs`), which lets the higher-order unifier discharge the
/// projection types the CertVerifier reasons about — so a genuinely-valid
/// linarith proof is now accepted. The negative companion
/// (`test_verify_proof_rejects_ill_typed_typeclass_proof`) still rejects an
/// ill-typed proof, so this is sound (no false-accept).
///
/// Re: #2150, Re: #2153.
#[test]
fn test_verify_proof_cert_verifier_projection_gap() {
    use crate::tactic::arith_linarith::{build_linarith_proof, LinarithCertificate};

    let env = Environment::with_prelude();
    let false_const = Expr::const_(Name::from_string("False"), vec![]);
    let h_id = FVarId::new(0);
    let h_ty = make_nat_le_tc(Expr::nat_lit(3), Expr::nat_lit(2));
    let state = ProofState::with_context(
        env.clone(),
        false_const,
        vec![LocalDecl {
            fvar: h_id,
            name: "h".into(),
            ty: h_ty,
            value: None,
        }],
    );
    let goal = state.current_goal().expect("should have a goal");
    let certificate = LinarithCertificate {
        coefficients: vec![1, 0],
        result_constant: 1,
    };
    let proof = build_linarith_proof(&state, goal, &certificate, &[h_id])
        .expect("should produce a proof term");

    let result = state.verify_proof(goal, &proof);
    assert!(
        result.is_ok(),
        "verify_proof should now accept a valid linarith proof whose type \
         carries typeclass projections (gap closed by the Pi/Lam binder-opening \
         in the higher-order unifier); got {result:?}"
    );
}

/// Negative case: verify_proof rejects ill-typed proof with typeclass types.
///
/// Given a False goal, using a hypothesis of type @LE.le Nat instLENat 3 2
/// directly (without False.elim wrapping) must be rejected by verify_proof,
/// even when the inferred type is WHNF-normalized.
///
/// Re: #2153.
#[test]
fn test_verify_proof_rejects_ill_typed_typeclass_proof() {
    let env = Environment::with_prelude();
    let false_const = Expr::const_(Name::from_string("False"), vec![]);
    let h_id = FVarId::new(0);
    let h_ty = make_nat_le_tc(Expr::nat_lit(3), Expr::nat_lit(2));
    let state = ProofState::with_context(
        env,
        false_const,
        vec![LocalDecl {
            fvar: h_id,
            name: "h".into(),
            ty: h_ty,
            value: None,
        }],
    );
    let goal = state.current_goal().expect("should have a goal");

    let proof = Expr::fvar(h_id);
    let result = state.verify_proof(goal, &proof);
    assert!(
        matches!(
            result,
            Err(TacticError::TypeMismatch { .. }) | Err(TacticError::TypeCheckFailed(_))
        ),
        "verify_proof must reject proof of type @LE.le Nat instLENat 3 2 for False goal, got: {result:?}"
    );
}
