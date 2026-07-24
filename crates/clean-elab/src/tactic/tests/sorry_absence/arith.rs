// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
#[serial]
fn test_linarith_sorry_count_on_transitivity() {
    // Goal: x <= z with h1: x <= y, h2: y <= z (Nat)
    //
    // PROOF QUALITY: linarith's fallback chain is:
    //   build_linarith_proof() -> close_goal() -> decide() -> create_trusted_arith_term()
    //
    // With correct LE instance (@LE.le.{0} Nat instLENat), close_goal
    // can accept the proof term from build_linarith_proof. The #2150 fix
    // (WHNF normalization in is_def_eq) enables LE.le → Nat.le reduction.
    reset_all_counters();
    let mut state = setup_linarith_transitivity();

    let result = linarith(&mut state);

    let sorry_used = sorry_count();
    let arith_used = arith_proof_count();
    let ay_used = ay_proof_count();

    assert!(
        result.is_ok(),
        "linarith must succeed on transitivity (x <= y, y <= z ⊢ x <= z): {:?}",
        result.err()
    );
    assert_eq!(
        sorry_used, 0,
        "linarith succeeded but used {} sorry terms",
        sorry_used
    );

    // With correct instLENat and #2150 WHNF normalization, the proof should
    // pass close_goal without falling through to trustedArith/trustedAy.
    // Part of #2442 Phase 3: promote informational log to hard assertion.
    assert_eq!(
        ay_used, 0,
        "REGRESSION: linarith transitivity produced {} trustedAy terms (expected 0). \
         With #2150 WHNF normalization, close_goal should accept the proof directly.",
        ay_used
    );
    let total_non_kernel = sorry_used + arith_used + ay_used;
    if total_non_kernel > 0 {
        eprintln!(
            "KNOWN GAP: linarith used sorry={}, trustedArith={}, trustedAy={} \
             on transitivity with correct LE instance (Part of #1144)",
            sorry_used, arith_used, ay_used
        );
    }
}

/// AC2 (#2124): build_linarith_proof proof terms pass kernel type-checking.
#[test]
fn test_linarith_proof_term_type_checks_ac2() {
    use crate::tactic::arith_linarith::{build_linarith_proof, LinarithCertificate};
    use clean_kernel::{BinderInfo, LocalContext};

    let env = Environment::with_prelude();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let (x_id, y_id, z_id) = (FVarId::new(0), FVarId::new(1), FVarId::new(2));
    let (h1_id, h2_id) = (FVarId::new(3), FVarId::new(4));
    let h1_ty = make_nat_le_tc(Expr::fvar(x_id), Expr::fvar(y_id));
    let h2_ty = make_nat_le_tc(Expr::fvar(y_id), Expr::fvar(z_id));
    let goal_ty = make_nat_le_tc(Expr::fvar(x_id), Expr::fvar(z_id));
    let mut local_ctx = LocalContext::new();
    for (id, name, ty) in [
        (x_id, "x", nat.clone()),
        (y_id, "y", nat.clone()),
        (z_id, "z", nat.clone()),
        (h1_id, "h1", h1_ty.clone()),
        (h2_id, "h2", h2_ty.clone()),
    ] {
        local_ctx.push_with_id(id, Name::from_string(name), ty, BinderInfo::Default);
    }
    let state = ProofState::with_context(
        env.clone(),
        goal_ty,
        vec![
            LocalDecl {
                fvar: x_id,
                name: "x".into(),
                ty: nat.clone(),
                value: None,
            },
            LocalDecl {
                fvar: y_id,
                name: "y".into(),
                ty: nat.clone(),
                value: None,
            },
            LocalDecl {
                fvar: z_id,
                name: "z".into(),
                ty: nat,
                value: None,
            },
            LocalDecl {
                fvar: h1_id,
                name: "h1".into(),
                ty: h1_ty,
                value: None,
            },
            LocalDecl {
                fvar: h2_id,
                name: "h2".into(),
                ty: h2_ty,
                value: None,
            },
        ],
    );
    let goal = state.current_goal().expect("should have a goal");
    let certificate = LinarithCertificate {
        coefficients: vec![1, 1, 1],
        result_constant: 0,
    };
    let proof = build_linarith_proof(&state, goal, &certificate, &[h1_id, h2_id]);
    assert!(
        proof.is_some(),
        "build_linarith_proof must return Some for transitivity"
    );
    let tc = TypeChecker::with_context(&env, local_ctx);
    let inferred = tc
        .infer_type(&proof.unwrap())
        .expect("AC2: proof must type-check");
    let expected = make_nat_le_tc(Expr::fvar(x_id), Expr::fvar(z_id));
    assert_eq!(
        inferred, expected,
        "AC2: proof type must match goal (x <= z)"
    );
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NlinarithOutcome {
    Success,
    ArithmeticFailed,
    Panic,
}

/// Measured on clean HEAD 2026-03-13. Tightening order: Panic -> ArithmeticFailed -> Success.
const NLINARITH_TRANSITIVITY_OUTCOME_RATCHET: NlinarithOutcome = NlinarithOutcome::Success;

fn classify_nlinarith_outcome(
    result: Result<Result<(), TacticError>, Box<dyn std::any::Any + Send>>,
) -> NlinarithOutcome {
    match result {
        Ok(Ok(())) => NlinarithOutcome::Success,
        Ok(Err(TacticError::ArithmeticFailed { .. })) => NlinarithOutcome::ArithmeticFailed,
        Err(_) => NlinarithOutcome::Panic,
        Ok(Err(e)) => panic!("nlinarith: unexpected error variant: {e:?}"),
    }
}

#[test]
#[serial]
fn test_nlinarith_sorry_count_on_transitivity() {
    // Goal: x <= z with h1: x <= y, h2: y <= z (Nat)
    reset_all_counters();
    let mut state = setup_linarith_transitivity();

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| nlinarith(&mut state)));
    let sorry_used = sorry_count();
    let arith_used = arith_proof_count();
    let ay_used = ay_proof_count();
    let observed = classify_nlinarith_outcome(result);

    assert_eq!(
        observed, NLINARITH_TRANSITIVITY_OUTCOME_RATCHET,
        "nlinarith transitivity outcome changed: expected {NLINARITH_TRANSITIVITY_OUTCOME_RATCHET:?}, \
         got {observed:?} (sorry={sorry_used}, arith={arith_used}, ay={ay_used}). \
         If intentional, update NLINARITH_TRANSITIVITY_OUTCOME_RATCHET."
    );
    match observed {
        NlinarithOutcome::Success => {
            assert_eq!(
                sorry_used, 0,
                "nlinarith succeeded but used {sorry_used} sorry terms"
            );
            assert_eq!(
                arith_used + ay_used,
                0,
                "nlinarith succeeded but used non-kernel proofs (arith={arith_used}, ay={ay_used})"
            );
        }
        NlinarithOutcome::ArithmeticFailed | NlinarithOutcome::Panic => {
            let label = if observed == NlinarithOutcome::ArithmeticFailed {
                "errored"
            } else {
                "panicked"
            };
            assert_all_counters_zero_on_failure(
                "nlinarith",
                label,
                sorry_used,
                arith_used,
                ay_used,
            );
        }
    }
}
