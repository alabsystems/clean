// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the test-only `replace_target_with_witness` compatibility helper
//! and `TargetRewriteWitness`.
//!
//! Coverage per design doc `designs/2026-03-11-2500-replace-target-proof-carry-api.md`:
//!
//! 1. `defeq` fast path through `replace_target_with_witness`
//! 2. Explicit proof path via `EqualityProof`
//! 3. Invalid proof path — error propagates, no silent trusted fallback
//! 4. Wrapper parity — `replace_target_with_trusted_fallback` behaves identically
//!
//! Part of #2500.

use super::*;
use clean_kernel::env::Declaration;
use serial_test::serial;

fn add_axiom(env: &mut Environment, name: &str, type_: Expr) {
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
    })
    .unwrap();
}

fn assert_no_trusted_fallback(state: &ProofState, tactic_name: &str, before: (u64, u64)) {
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "{tactic_name} must not record trusted axiom usage"
    );
    assert_no_trusted_axiom_usage(tactic_name, "replace-target witness path", before);
}

// =============================================================================
// 1. DefEq fast path
// =============================================================================

/// The `TrustedFallback` variant should take the def-eq fast path when the
/// new target is definitionally equal, recording zero trusted axiom usage.
#[test]
#[serial]
fn test_witness_trusted_fallback_takes_defeq_fast_path() {
    reset_all_counters();
    let mut env = Environment::new();
    env.init_eq().unwrap();

    add_axiom(&mut env, "P", Expr::prop());

    // MyProp := P (reducible, so def-eq to P)
    env.add_decl(Declaration::Definition {
        name: Name::from_string("MyProp"),
        level_params: vec![],
        type_: Expr::prop(),
        value: Expr::const_(Name::from_string("P"), vec![]),
        is_reducible: true,
    })
    .unwrap();

    let my_prop = Expr::const_(Name::from_string("MyProp"), vec![]);
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let mut state = ProofState::new(env, my_prop);
    let axiom_before = axiom_snapshot();

    let result = state.replace_target_with_witness(
        p.clone(),
        TargetRewriteWitness::TrustedFallback {
            tactic_name: "test",
        },
    );
    assert!(
        result.is_ok(),
        "defeq fast path should succeed, got: {result:?}"
    );
    assert_no_trusted_fallback(&state, "defeq fast path", axiom_before);
    assert_eq!(
        state.current_goal().unwrap().target,
        p,
        "target should be rewritten to P"
    );
}

/// The `EqualityProof` variant should also take the def-eq fast path when
/// the new target is definitionally equal, ignoring the supplied proof.
#[test]
#[serial]
fn test_witness_equality_proof_takes_defeq_fast_path() {
    reset_all_counters();
    let mut env = Environment::new();
    env.init_eq().unwrap();

    add_axiom(&mut env, "P", Expr::prop());
    env.add_decl(Declaration::Definition {
        name: Name::from_string("MyProp"),
        level_params: vec![],
        type_: Expr::prop(),
        value: Expr::const_(Name::from_string("P"), vec![]),
        is_reducible: true,
    })
    .unwrap();

    let my_prop = Expr::const_(Name::from_string("MyProp"), vec![]);
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let mut state = ProofState::new(env, my_prop);

    // Supply a dummy proof that won't be used (def-eq path short-circuits)
    let dummy_proof = Expr::const_(Name::from_string("P"), vec![]);
    let result = state.replace_target_with_witness(
        p.clone(),
        TargetRewriteWitness::EqualityProof {
            tactic_name: "test",
            eq_proof: dummy_proof,
        },
    );
    assert!(
        result.is_ok(),
        "defeq fast path should succeed with EqualityProof variant, got: {result:?}"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "defeq fast path must not record trusted axiom usage"
    );
}

// =============================================================================
// 2. Explicit proof path
// =============================================================================

/// The `EqualityProof` variant replaces the target via `Eq.mpr` and does
/// not touch the trusted axiom accounting.
#[test]
#[serial]
fn test_witness_equality_proof_path() {
    reset_all_counters();
    let mut env = Environment::new();
    env.init_eq().unwrap();

    let prop_p = Expr::const_(Name::from_string("P"), vec![]);
    let prop_q = Expr::const_(Name::from_string("Q"), vec![]);
    add_axiom(&mut env, "P", Expr::prop());
    add_axiom(&mut env, "Q", Expr::prop());
    add_axiom(&mut env, "hq", prop_q.clone());

    // eq_proof : P = Q (via Eq.refl at Prop level on P = Q identity — use
    // a trusted axiom to construct a synthetic proof for test purposes)
    // Actually, we need a real `@Eq Prop P Q` proof. Build one via trustedArith
    // but don't go through the wrapper — construct it manually for the test.
    use crate::tactic::arith_linarith::make_trusted_arith_term_untracked;
    let eq_ty = make_eq(Expr::prop(), prop_p.clone(), prop_q.clone());
    let eq_proof = make_trusted_arith_term_untracked(&env, &eq_ty);

    let mut state = ProofState::new(env, prop_p);

    let result = state.replace_target_with_witness(
        prop_q.clone(),
        TargetRewriteWitness::EqualityProof {
            tactic_name: "test_tactic",
            eq_proof,
        },
    );
    assert!(
        result.is_ok(),
        "EqualityProof path should succeed, got: {result:?}"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "EqualityProof path must not increment per-state trusted axiom count"
    );
    assert_eq!(
        state.current_goal().unwrap().target,
        prop_q,
        "target should be rewritten to Q"
    );

    // Close the goal and verify proof chain
    exact(&mut state, Expr::const_(Name::from_string("hq"), vec![]))
        .expect("exact hq should close the rewritten goal");
    assert!(state.is_complete(), "proof should be complete");
    assert!(
        state.proof_term().is_some(),
        "proof_term() must stay connected through EqualityProof path"
    );
    assert!(
        state.closed_proof().is_some(),
        "closed_proof() must be extractable after EqualityProof path"
    );
}

// =============================================================================
// 3. Invalid proof path — error propagates, no silent trusted fallback
// =============================================================================

/// When `EqualityProof` carries an ill-typed proof, the error must propagate
/// without falling through to `trustedArith`. This is the key soundness
/// property from design section 4.
#[test]
#[serial]
fn test_witness_equality_proof_invalid_does_not_fall_through() {
    reset_all_counters();
    let mut env = Environment::new();
    env.init_eq().unwrap();

    let prop_p = Expr::const_(Name::from_string("P"), vec![]);
    let prop_q = Expr::const_(Name::from_string("Q"), vec![]);
    add_axiom(&mut env, "P", Expr::prop());
    add_axiom(&mut env, "Q", Expr::prop());

    let mut state = ProofState::new(env, prop_p.clone());
    let axiom_before = axiom_snapshot();

    // Supply a proof that doesn't have type `P = Q` — just use `P` itself.
    // Wave 97 (Gap 18): `replace_target_eq` now kernel-typechecks the
    // supplied witness against `@Eq.{succ u} (Sort u) old new` before
    // mutating the goal, so this MUST fail.
    let bad_proof = Expr::const_(Name::from_string("P"), vec![]);
    let result = state.replace_target_with_witness(
        prop_q,
        TargetRewriteWitness::EqualityProof {
            tactic_name: "bad_tactic",
            eq_proof: bad_proof,
        },
    );
    assert!(
        result.is_err(),
        "replace_target_with_witness must reject an invalid equality proof: {result:?}"
    );
    assert_eq!(
        state.current_goal().unwrap().target,
        prop_p,
        "failed EqualityProof must not mutate the goal target"
    );
    assert_no_trusted_fallback(&state, "failed EqualityProof", axiom_before);
}

/// Wave 97 — Gap 18 negative test. A *swapped-orientation* equality
/// proof (`@Eq Prop Q P` when we want `@Eq Prop P Q`) must also be
/// rejected: the kernel check pins down argument order, not just the
/// head connective. Without this guard, callers could rewrite in the
/// wrong direction without the kernel noticing.
#[test]
#[serial]
fn test_witness_equality_proof_swapped_orientation_is_rejected() {
    reset_all_counters();
    let mut env = Environment::new();
    env.init_eq().unwrap();

    let prop_p = Expr::const_(Name::from_string("P"), vec![]);
    let prop_q = Expr::const_(Name::from_string("Q"), vec![]);
    add_axiom(&mut env, "P", Expr::prop());
    add_axiom(&mut env, "Q", Expr::prop());
    // h : @Eq Prop Q P — opposite orientation from what `replace_target_eq` expects.
    let h_ty = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                Expr::prop(),
            ),
            prop_q.clone(),
        ),
        prop_p.clone(),
    );
    add_axiom(&mut env, "h_qp", h_ty);

    let mut state = ProofState::new(env, prop_p.clone());
    let axiom_before = axiom_snapshot();
    let result = state.replace_target_with_witness(
        prop_q.clone(),
        TargetRewriteWitness::EqualityProof {
            tactic_name: "swapped_tactic",
            eq_proof: Expr::const_(Name::from_string("h_qp"), vec![]),
        },
    );
    assert!(
        result.is_err(),
        "replace_target_with_witness must reject swapped-orientation proof: {result:?}"
    );
    assert_eq!(
        state.current_goal().unwrap().target,
        prop_p,
        "swapped-orientation witness must not mutate the goal"
    );
    assert_no_trusted_fallback(&state, "swapped EqualityProof", axiom_before);
}

// =============================================================================
// 4. Wrapper parity — replace_target_with_trusted_fallback via witness
// =============================================================================

/// The thin wrapper `replace_target_with_trusted_fallback` must produce the
/// same accounting as the direct `TrustedFallback` witness path.
#[test]
#[serial]
fn test_wrapper_parity_trusted_fallback_accounting() {
    use crate::tactic::arith_linarith::enable_arith_location_tracking;

    reset_all_counters();
    let mut env = Environment::new();
    env.init_eq().unwrap();

    let prop_p = Expr::const_(Name::from_string("P"), vec![]);
    let prop_q = Expr::const_(Name::from_string("Q"), vec![]);
    add_axiom(&mut env, "P", Expr::prop());
    add_axiom(&mut env, "Q", Expr::prop());
    add_axiom(&mut env, "hq", prop_q.clone());

    let mut state = ProofState::new(env, prop_p);
    let axiom_before = axiom_snapshot();
    enable_arith_location_tracking();
    let helper_key = "helper:replace_target_with_trusted_fallback:simp";
    let helper_before = tracked_arith_location_count(helper_key);
    let direct_before = direct_arith_file_count(file!());

    state
        .replace_target_with_trusted_fallback(prop_q.clone(), "simp")
        .expect("wrapper should rewrite P to Q via trusted fallback");
    assert_eq!(
        state.trusted_axiom_count(),
        1,
        "wrapper must record exactly one trusted axiom use"
    );
    assert_eq!(
        state.current_goal().unwrap().target,
        prop_q,
        "wrapper should leave the rewritten target active"
    );
    assert_eq!(
        axiom_snapshot().0 - axiom_before.0,
        1,
        "wrapper must increment the global trustedArith counter exactly once"
    );
    assert_eq!(
        tracked_arith_location_count(helper_key),
        helper_before + 1,
        "wrapper should record helper provenance instead of a helper file line"
    );
    assert_eq!(
        direct_arith_file_count(file!()),
        direct_before,
        "wrapper should not collapse helper traffic into the test callsite line"
    );

    exact(&mut state, Expr::const_(Name::from_string("hq"), vec![]))
        .expect("exact hq should close the rewritten goal");
    assert!(state.is_complete(), "proof should be complete");
    assert!(
        state.proof_term().is_some(),
        "proof_term() must stay connected through the wrapper"
    );
    assert!(
        state.closed_proof().is_some(),
        "closed_proof() must be extractable through the wrapper"
    );
}

/// The wrapper must propagate errors from missing `Eq` without recording
/// trusted fallback usage.
#[test]
#[serial]
fn test_wrapper_parity_missing_eq_propagates() {
    reset_all_counters();
    let mut env = Environment::new();

    let prop_p = Expr::const_(Name::from_string("P"), vec![]);
    let prop_q = Expr::const_(Name::from_string("Q"), vec![]);
    add_axiom(&mut env, "P", Expr::prop());
    add_axiom(&mut env, "Q", Expr::prop());

    let mut state = ProofState::new(env, prop_p.clone());

    let result = state.replace_target_with_trusted_fallback(prop_q, "simp");
    assert!(
        matches!(result, Err(TacticError::EnvironmentMissing { ref constant }) if constant == "Eq"),
        "wrapper must propagate EnvironmentMissing(Eq), got: {result:?}"
    );
    assert_eq!(
        state.current_goal().unwrap().target,
        prop_p,
        "failed wrapper must not mutate the goal target"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "failed wrapper must not record trusted fallback"
    );
}
