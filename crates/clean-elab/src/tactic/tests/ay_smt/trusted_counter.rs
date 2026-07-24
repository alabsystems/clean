// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// 4. ¬(P ∧ ¬P) (non-contradiction)
#[test]
fn test_ay_prop_non_contradiction() {
    let env = setup_ay_env();
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let target = ay_make_not(ay_make_and(p.clone(), ay_make_not(p)));

    let mut state = ProofState::new(env, target);
    ay_decide(&mut state, AyConfig::default()).expect("ay should prove ¬(P ∧ ¬P)");
    assert!(state.is_complete());
    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        0,
        "¬(P ∧ ¬P) should close without trustedAy"
    );
}

/// 7. h: ¬(P ∧ Q) ⊢ ¬P ∨ ¬Q (De Morgan via hypothesis)
#[test]
fn test_ay_prop_de_morgan_and() {
    let env = setup_ay_env();
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let h_fvar = FVarId::new(1);

    let mut state = ProofState::with_context(
        env,
        ay_make_or(ay_make_not(p.clone()), ay_make_not(q.clone())),
        vec![LocalDecl {
            fvar: h_fvar,
            name: "h".to_string(),
            ty: ay_make_not(ay_make_and(p, q)),
            value: None,
        }],
    );
    ay_decide(&mut state, AyConfig::default()).expect("ay should prove De Morgan (∧)");
    assert!(state.is_complete());
    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        0,
        "De Morgan on conjunction should close without trustedAy"
    );
}

/// 19. Ground Nat comparison goals should stay kernel-checked.
#[test]
fn test_ay_counter_stays_zero_on_ground_nat_solve() {
    let env = setup_ay_env();

    let target = ay_make_nat_le(Expr::nat_lit(0), Expr::nat_lit(1));
    let mut state = ProofState::new(env, target);

    ay_omega(&mut state, AyConfig::default()).expect("ay should prove 0 ≤ 1");
    assert!(state.is_complete());

    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        0,
        "ground Nat <= goal should close without trustedAy"
    );
}

/// 20. Simple `ay_bv` equality goals should stay kernel-checked.
#[test]
fn test_ay_bv_counter_stays_zero_on_simple_equality() {
    let env = setup_ay_env();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let target = ay_make_eq(nat_ty, Expr::nat_lit(42), Expr::nat_lit(42));
    let mut state = ProofState::new(env, target);

    ay_bv(&mut state, AyConfig::default()).expect("ay_bv should prove 42 = 42");
    assert!(state.is_complete());

    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        0,
        "simple ay_bv equality should close without trustedAy"
    );
}

/// VerifyStrict does not accept the ay QF_BV proof lane. It should reject that
/// lane before proof acceptance and then reuse the native fallback path.
#[test]
#[serial]
fn test_ay_bv_verifystrict_rejects_ay_lane_and_falls_back_without_trusted_ay() {
    let env = setup_ay_env();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let target = ay_make_eq(nat_ty, Expr::nat_lit(42), Expr::nat_lit(42));

    reset_local_ay_reconstruction_success_counter();
    let mut state = ProofState::new(env, target);
    let config = AyConfig::default().with_verify_policy(SmtVerifyPolicy::VerifyStrict);

    ay_bv(&mut state, config)
        .expect("VerifyStrict QF_BV should reject the ay proof lane and fall back to decide");
    assert!(state.is_complete());
    assert!(
        state.proof_term().is_some(),
        "fallback should still produce a proof term"
    );
    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        0,
        "strict QF_BV fallback must not accept any ay-derived trust debt"
    );
    assert_eq!(
        local_ay_reconstruction_success_count(),
        0,
        "strict QF_BV should reject the ay proof lane before any ay reconstruction is accepted"
    );
}

// =========================================================================
// Reconstruction success counter at the post-gate boundary (Part of #302)
// =========================================================================
//
// These tests verify that the thread-local reconstruction-success view
// increments when ay proof reconstruction or bridge fallback produces a
// kernel proof term on the current test thread. The underlying global metric
// remains process-wide; the local view keeps these assertions stable under the
// parallel lib suite. The counter seam is still
// `finalize_reconstructed_unsat_proof` / `try_bridge_reconstruction` per the
// #302 handoff.

use crate::tactic::smt::SmtVerifyPolicy;
use clean_kernel::sorry::{
    local_ay_reconstruction_success_count, reset_local_ay_reconstruction_success_counter,
};
use serial_test::serial;

/// Supported Prop-FVar tautology via ExtractOnly: reconstruction counter must increment.
///
/// This is the stable tactic-level ay/bridge case after #2787. Bare proposition
/// constants can fail closed and fall back to native `decide`, but a registered
/// Prop FVar tautology stays on the proof-producing SMT lane and should record
/// reconstruction success without touching trustedAy. Part of #2900.
#[test]
#[serial]
fn test_ay_decide_extract_only_reconstruction_counter_on_supported_tautology() {
    let env = setup_ay_env();
    let (p, p_decl) = prop_local_decl(95, "p");
    let target = ay_make_or(p.clone(), ay_make_not(p));

    reset_local_ay_reconstruction_success_counter();
    let mut state = ProofState::with_context(env, target, vec![p_decl]);

    let config = AyConfig::default().with_verify_policy(SmtVerifyPolicy::ExtractOnly);
    ay_decide(&mut state, config).expect("ay ExtractOnly should prove P ∨ ¬P");
    assert!(state.is_complete(), "goal should be closed");

    assert_eq!(
        state.trust_ledger().trusted_ay_count,
        0,
        "supported Prop-FVar tautology should close without trustedAy"
    );

    let recon_count = local_ay_reconstruction_success_count();
    assert!(
        recon_count >= 1,
        "supported Prop-FVar tautology should increment the local ay reconstruction counter; got {recon_count}"
    );
}
