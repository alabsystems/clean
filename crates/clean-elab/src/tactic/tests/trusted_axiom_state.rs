// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for per-proof trust tracking on `ProofState`.
//!
//! These cover both the legacy total counter and the typed trust ledger used by
//! server trust summaries.

use super::*;
use crate::tactic::core::ProofTrustLedger;
use clean_auto::bridge::ay_contract::test_utils::residual_trust_summary_from_source;
use clean_auto::bridge::ay_contract::ResidualTrustSource;
use clean_kernel::env::Declaration;
use serial_test::serial;

// reset_all_counters is now a shared helper in tests/mod.rs

fn setup_env_with_parity() -> Environment {
    let mut env = Environment::with_prelude();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    for name in ["Even", "Odd"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::arrow(nat.clone(), Expr::prop()),
        })
        .unwrap();
    }
    env
}

fn setup_env_with_prop_atom() -> Environment {
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("add P axiom");
    env
}

/// Verify theorem-missing parity contradictions fail closed without recording
/// trusted axioms.
#[test]
#[serial]
fn test_mathverse_parity_fail_closed_without_trusted_axioms() {
    reset_all_counters();
    let env = setup_env_with_parity();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let n_fvar = FVarId::new(0);

    let mut state = ProofState::with_context(
        env,
        Expr::const_(Name::from_string("False"), vec![]),
        vec![
            LocalDecl {
                fvar: n_fvar,
                name: "n".to_string(),
                ty: nat,
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(1),
                name: "h_even".to_string(),
                ty: Expr::app(
                    Expr::const_(Name::from_string("Even"), vec![]),
                    Expr::fvar(n_fvar),
                ),
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(2),
                name: "h_odd".to_string(),
                ty: Expr::app(
                    Expr::const_(Name::from_string("Odd"), vec![]),
                    Expr::fvar(n_fvar),
                ),
                value: None,
            },
        ],
    );

    assert_eq!(state.trusted_axiom_count(), 0);
    let axiom_before = axiom_snapshot();
    let result = omega(&mut state);

    let global_arith = axiom_snapshot().0 - axiom_before.0;
    let state_count = state.trusted_axiom_count();

    assert!(
        matches!(result, Err(TacticError::ArithmeticFailed { ref tactic, .. }) if tactic == "mathverse"),
        "mathverse should fail closed on bare Even/Odd axioms, got: {result:?}"
    );
    assert_eq!(
        global_arith, 0,
        "mathverse must not use trustedArith on unsupported modular replay"
    );
    assert_eq!(
        state_count, 0,
        "fail-closed mathverse must not record trusted axioms"
    );
    assert!(
        !state.is_complete(),
        "goal must remain open after fail-closed mathverse parity replay"
    );
    let ledger = state.trust_ledger();
    assert_eq!(ledger.sorry_count, 0);
    assert_eq!(ledger.trusted_ay_count, 0);
    assert_eq!(ledger.trusted_arith_count, 0);
}

/// Verify close_with_trusted_arith increments both global and per-state counters.
///
/// Tests the tracking function directly: linarith's trustedArith fallback path
/// is unreachable when the SMT-backed `decide` handles the goal first, so we
/// exercise close_with_trusted_arith on an arbitrary goal. This verifies that
/// goal-level trust accounting stays in sync with the emitted proof term.
#[test]
#[serial]
fn test_trusted_axiom_count_tracks_close_with_trusted_arith() {
    use crate::tactic::arith_linarith::{close_with_trusted_arith, enable_arith_location_tracking};
    reset_all_counters();
    let env = Environment::with_prelude();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let (x, y) = (FVarId::new(0), FVarId::new(1));
    let goal_ty = make_nat_le_tc(Expr::fvar(x), Expr::fvar(y));

    let mut state = ProofState::with_context(
        env,
        goal_ty,
        vec![
            LocalDecl {
                fvar: x,
                name: "x".into(),
                ty: nat.clone(),
                value: None,
            },
            LocalDecl {
                fvar: y,
                name: "y".into(),
                ty: nat,
                value: None,
            },
        ],
    );

    assert_eq!(state.trusted_axiom_count(), 0);
    let axiom_before = axiom_snapshot();
    enable_arith_location_tracking();
    let helper_key = "helper:close_with_trusted_arith:linarith";
    let helper_before = tracked_arith_location_count(helper_key);
    let direct_before = direct_arith_file_count(file!());

    let goal = state.current_goal().unwrap().clone();
    close_with_trusted_arith(&mut state, &goal, "linarith", "test: forced fallback")
        .expect("close_with_trusted_arith should succeed");

    let global_arith = axiom_snapshot().0 - axiom_before.0;
    let state_count = state.trusted_axiom_count();

    assert!(
        global_arith > 0,
        "close_with_trusted_arith should increment global arith_proof_count, got 0"
    );
    assert_eq!(
        state_count as u64, global_arith,
        "TRACKING GAP: global arith_proof_count={global_arith} but \
         ProofState.trusted_axiom_count={state_count}"
    );
    let ledger = state.trust_ledger();
    assert_eq!(ledger.sorry_count, 0);
    assert_eq!(ledger.trusted_ay_count, 0);
    assert_eq!(ledger.trusted_arith_count as u64, global_arith);
    assert_eq!(
        ledger.trusted_arith_provenance.goal_close_helper_steps as u64, global_arith,
        "goal-close helper provenance should preserve the trustedArith total"
    );
    assert_eq!(ledger.trusted_arith_provenance.direct_steps, 0);
    assert_eq!(
        ledger.trusted_arith_provenance.target_rewrite_helper_steps,
        0
    );
    assert_eq!(ledger.trusted_arith_provenance.unclassified_steps, 0);
    assert_eq!(
        tracked_arith_location_count(helper_key),
        helper_before + 1,
        "close_with_trusted_arith should record helper provenance by tactic name"
    );
    assert_eq!(
        direct_arith_file_count(file!()),
        direct_before,
        "close_with_trusted_arith should not collapse helper traffic into the callsite line"
    );
}

#[test]
fn test_record_trusted_arith_provenance_categories_preserve_total() {
    let mut state = ProofState::new(Environment::with_prelude(), Expr::prop());

    state.record_trusted_arith_direct(2);
    state.record_trusted_arith();

    let ledger = state.trust_ledger();
    assert_eq!(ledger.trusted_arith_count, 3);
    assert_eq!(ledger.trusted_arith_provenance.direct_steps, 2);
    assert_eq!(ledger.trusted_arith_provenance.goal_close_helper_steps, 0);
    assert_eq!(
        ledger.trusted_arith_provenance.target_rewrite_helper_steps,
        0
    );
    assert_eq!(ledger.trusted_arith_provenance.unclassified_steps, 1);
}

#[test]
fn test_record_trusted_ay_or_sorry_uses_sorry_without_axiom() {
    let mut state = ProofState::new(Environment::default(), Expr::prop());

    smt::record_trusted_ay_or_sorry(&mut state);

    let ledger = state.trust_ledger();
    assert_eq!(ledger.sorry_count, 1);
    assert_eq!(ledger.trusted_ay_count, 0);
    assert_eq!(ledger.trusted_arith_count, 0);
}

#[test]
fn test_record_trusted_ay_or_sorry_uses_trusted_ay_with_axiom() {
    let mut env = Environment::new();
    env.init_trusted_ay()
        .expect("trustedAy axiom should initialize");
    let mut state = ProofState::new(env, Expr::prop());

    smt::record_trusted_ay_or_sorry(&mut state);

    let ledger = state.trust_ledger();
    assert_eq!(ledger.sorry_count, 0);
    assert_eq!(ledger.trusted_ay_count, 1);
    assert_eq!(ledger.trusted_arith_count, 0);
    assert_eq!(ledger.trusted_ay_provenance.unclassified_steps, 1);
    assert_eq!(ledger.trusted_ay_provenance.typed_total(), 0);
}

#[test]
#[serial]
fn test_force_trusted_ay_fail_closed_keeps_trust_ledger_zero() {
    reset_all_counters();
    let target = Expr::const_(Name::from_string("P"), vec![]);
    let mut state = ProofState::new(setup_env_with_prop_atom(), target.clone());
    let goal = state.current_goal().expect("goal").clone();
    let axiom_before = axiom_snapshot();

    let result = smt::force_trusted_ay_fail_closed_for_test(&mut state, &goal, &target);

    assert!(
        matches!(
            result,
            Err(TacticError::SmtFailed { ref tactic, ref detail })
                if tactic == "decide"
                    && detail.contains("test-only forced fail-closed outcome")
        ),
        "forced fail-closed helper should surface a structured SMT error, got: {result:?}"
    );
    assert_eq!(
        axiom_snapshot().1 - axiom_before.1,
        0,
        "forced fail-closed helper must not emit whole-goal trustedAy"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "forced fail-closed helper must not record trusted axioms"
    );
    assert!(
        !state.is_complete(),
        "goal should remain open after forced fail-closed shared recovery"
    );
    let ledger = state.trust_ledger();
    assert_eq!(ledger.sorry_count, 0);
    assert_eq!(ledger.trusted_ay_count, 0);
    assert_eq!(ledger.trusted_arith_count, 0);
}

#[test]
#[serial]
fn test_sorry_tactic_uses_explicit_sorry_provenance_with_prelude() {
    reset_all_counters();
    let env = Environment::with_prelude();
    let mut state = ProofState::new(env, Expr::prop());

    // Snapshot global counters before the tactic call. Non-serial tests
    // running concurrently can increment global atomics, so delta-based
    // checking is required for reliable assertions.
    let explicit_before = clean_kernel::sorry::explicit_sorry_count();
    let synthetic_before = clean_kernel::sorry::synthetic_sorry_count();

    sorry(&mut state).expect("sorry should close the goal");

    assert!(state.is_complete(), "sorry should complete the proof state");

    let proof = state
        .proof_term()
        .expect("completed sorry proof should remain extractable");
    assert!(
        proof.is_non_synthetic_sorry(),
        "with Bool available, sorry should emit explicit sorryAx provenance"
    );
    assert!(
        !proof.has_synthetic_sorry(),
        "user-facing sorry must not route through the synthetic sorry lane"
    );

    let closed = state
        .closed_proof()
        .expect("closed sorry proof should remain extractable");
    assert!(
        closed.is_non_synthetic_sorry(),
        "closed proof should preserve explicit sorry provenance"
    );
    assert!(
        !closed.has_synthetic_sorry(),
        "closed proof should not contain synthetic sorry terms"
    );

    let ledger = state.trust_ledger();
    assert_eq!(
        ledger.sorry_count, 1,
        "sorry should record exactly one sorry"
    );
    assert_eq!(
        ledger.trusted_ay_count, 0,
        "sorry should not record trustedAy"
    );
    assert_eq!(
        ledger.trusted_arith_count, 0,
        "sorry should not record trustedArith"
    );
    let explicit_delta = clean_kernel::sorry::explicit_sorry_count() - explicit_before;
    let synthetic_delta = clean_kernel::sorry::synthetic_sorry_count() - synthetic_before;
    assert_eq!(
        explicit_delta, 1,
        "explicit sorry counter should track the term_close::sorry lane"
    );
    assert_eq!(
        synthetic_delta, 0,
        "term_close::sorry should stay out of the synthetic sorry bucket"
    );
}

/// Regression test for #2513: concurrent ProofStates must have independent
/// trust ledgers. Simulates the batch handler's parallel pattern with threads.
///
/// Must be `#[serial]` because spawned threads call `close_with_trusted_arith`
/// which increments the global arith counter. Without serialization this races
/// with other tests that assert on global counter deltas.
#[test]
#[serial]
fn test_trust_ledger_isolation_between_concurrent_proof_states() {
    use crate::tactic::arith_linarith::close_with_trusted_arith;
    use std::sync::Arc;
    use std::thread;

    let env = Arc::new(setup_env_with_parity());

    for _run in 0..4 {
        let mut handles: Vec<thread::JoinHandle<(String, ProofTrustLedger)>> = Vec::new();
        for i in 0..4 {
            let e = Arc::clone(&env);
            handles.push(thread::spawn(move || {
                let mut ps = ProofState::new((*e).clone(), Expr::prop());
                sorry(&mut ps).unwrap();
                (format!("clean-{i}"), ps.trust_ledger())
            }));
        }
        let e = Arc::clone(&env);
        handles.push(thread::spawn(move || {
            let mut ps = ProofState::new((*e).clone(), Expr::prop());
            let goal = ps.current_goal().expect("goal should exist").clone();
            close_with_trusted_arith(&mut ps, &goal, "mathverse", "test isolation trusted lane")
                .expect("forced trustedArith close should succeed");
            ("trusted".into(), ps.trust_ledger())
        }));

        for handle in handles {
            let (id, led): (String, ProofTrustLedger) = handle.join().unwrap();
            if id == "trusted" {
                assert_eq!(led.sorry_count, 0, "trusted item: no sorry");
                assert_eq!(led.trusted_ay_count, 0);
                assert!(
                    led.trusted_arith_count > 0,
                    "trusted item: trustedArith > 0"
                );
            } else {
                assert_eq!(led.sorry_count, 1, "clean item sorry=1: {id}");
                assert_eq!(led.trusted_ay_count, 0, "clean ay=0: {id}");
                assert_eq!(led.trusted_arith_count, 0, "clean arith=0: {id}");
            }
        }
    }
}

#[test]
fn test_trust_ledger_tracks_sorry_through_merge_meta_state() {
    let env = Environment::with_prelude();
    let mut parent = ProofState::new(env, Expr::prop());
    let goal = parent.current_goal().expect("goal should exist").clone();
    let mut focused = parent.clone_with_goal(goal);

    sorry(&mut focused).expect("sorry should close the focused goal");
    let focused_ledger = focused.trust_ledger();
    assert_eq!(focused_ledger.sorry_count, 1);
    assert_eq!(focused_ledger.trusted_ay_count, 0);
    assert_eq!(focused_ledger.trusted_arith_count, 0);

    parent.merge_meta_state(&focused);
    let parent_ledger = parent.trust_ledger();
    assert_eq!(parent_ledger.sorry_count, 1);
    assert_eq!(parent_ledger.trusted_ay_count, 0);
    assert_eq!(parent_ledger.trusted_arith_count, 0);
    assert_eq!(
        parent.trusted_axiom_count(),
        1,
        "legacy total should remain derived from the typed ledger"
    );
}

#[test]
fn test_trusted_axiom_count_saturates_instead_of_wrapping() {
    let ledger = ProofTrustLedger {
        sorry_count: u32::MAX,
        trusted_ay_count: 1,
        trusted_ay_provenance: TrustedAyProvenanceLedger {
            unclassified_steps: 1,
            ..TrustedAyProvenanceLedger::default()
        },
        trusted_arith_count: 1,
        trusted_arith_provenance: TrustedArithProvenanceLedger {
            unclassified_steps: 1,
            ..TrustedArithProvenanceLedger::default()
        },
        ..ProofTrustLedger::default()
    };

    assert_eq!(
        ledger.trusted_axiom_count(),
        u32::MAX,
        "trusted_axiom_count should saturate instead of wrapping"
    );
}

#[test]
fn test_record_sorry_saturates_at_u32_max() {
    let mut state = ProofState::new(Environment::with_prelude(), Expr::prop());
    state.set_trust_ledger(ProofTrustLedger {
        sorry_count: u32::MAX,
        ..ProofTrustLedger::default()
    });

    state.record_sorry();

    let ledger = state.trust_ledger();
    assert_eq!(
        ledger.sorry_count,
        u32::MAX,
        "record_sorry should saturate instead of wrapping"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        u32::MAX,
        "legacy trusted total should stay saturated after record_sorry"
    );
}

#[test]
fn test_merge_meta_state_adopts_exact_ay_provenance_branch() {
    let env = Environment::with_prelude();
    let mut parent = ProofState::new(env, Expr::prop());
    let goal = parent.current_goal().expect("goal should exist").clone();
    let mut focused = parent.clone_with_goal(goal);

    parent.record_trusted_ay_residual(
        1,
        residual_trust_summary_from_source(ResidualTrustSource::AletheTrustStep),
    );
    focused.record_trusted_ay_residual(
        1,
        residual_trust_summary_from_source(ResidualTrustSource::LocalReconstructionGap),
    );

    parent.merge_meta_state(&focused);
    let ledger = parent.trust_ledger();
    assert_eq!(ledger.trusted_ay_count, 1);
    assert_eq!(ledger.trusted_ay_provenance.alethe_trust_steps, 0);
    assert_eq!(ledger.trusted_ay_provenance.local_gap_steps, 1);
    assert_eq!(ledger.trusted_ay_provenance.unclassified_steps, 0);
}
