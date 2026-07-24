// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for nlinarith proof reconstruction.
//!
//! Part of #2531: the certified replay path should close reconstructible goals
//! without falling back to `trustedArith`.

use crate::tactic::arith_nlinarith::certified::{
    build_certified_nlinarith_proof, build_certified_nlinarith_replay_context,
    force_certified_nlinarith_no_kernel_proof, try_certified_nlinarith, CertifiedNlinarithOutcome,
};
use crate::tactic::arith_nlinarith::synthetic_rows::build_synthetic_row_decls;
use crate::tactic::tc_app::nat_lt_tc;

use super::*;
use serial_test::serial;

fn contradictory_nat_le_false_state() -> ProofState {
    let false_ty = Expr::const_(Name::from_string("False"), vec![]);
    let h_id = FVarId::new(0);
    let h_ty = make_nat_le_tc(Expr::nat_lit(5), Expr::nat_lit(3));
    ProofState::with_context(
        Environment::with_prelude(),
        false_ty,
        vec![LocalDecl {
            fvar: h_id,
            name: "h".into(),
            ty: h_ty,
            value: None,
        }],
    )
}

fn synthetic_row_source_state() -> ProofState {
    let x_id = FVarId::new(0);
    let hc_id = FVarId::new(1);
    let hx_id = FVarId::new(2);
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let false_ty = Expr::const_(Name::from_string("False"), vec![]);

    ProofState::with_context(
        Environment::with_prelude(),
        false_ty,
        vec![
            LocalDecl {
                fvar: x_id,
                name: "x".into(),
                ty: nat_ty,
                value: None,
            },
            LocalDecl {
                fvar: hc_id,
                name: "hc".into(),
                ty: make_nat_le_tc(Expr::nat_lit(0), Expr::nat_lit(2)),
                value: None,
            },
            LocalDecl {
                fvar: hx_id,
                name: "hx".into(),
                ty: make_nat_le_tc(Expr::fvar(x_id), Expr::nat_lit(0)),
                value: None,
            },
        ],
    )
}

fn nat_mul(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.mul"), vec![]), lhs),
        rhs,
    )
}

fn nat_add(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.add"), vec![]), lhs),
        rhs,
    )
}

fn goal_derived_synthetic_row_state() -> ProofState {
    let x_id = FVarId::new(0);
    let hc_id = FVarId::new(1);
    let hx_id = FVarId::new(2);
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);

    ProofState::with_context(
        Environment::with_prelude(),
        nat_lt_tc(Expr::nat_lit(0), Expr::fvar(x_id)),
        vec![
            LocalDecl {
                fvar: x_id,
                name: "x".into(),
                ty: nat_ty,
                value: None,
            },
            LocalDecl {
                fvar: hc_id,
                name: "hc".into(),
                ty: make_nat_le_tc(Expr::nat_lit(0), Expr::nat_lit(2)),
                value: None,
            },
            LocalDecl {
                fvar: hx_id,
                name: "hx".into(),
                ty: make_nat_le_tc(
                    Expr::nat_lit(1),
                    nat_mul(Expr::nat_lit(2), Expr::fvar(x_id)),
                ),
                value: None,
            },
        ],
    )
}

fn affine_synthetic_row_source_state() -> ProofState {
    let x_id = FVarId::new(0);
    let hc_id = FVarId::new(1);
    let hx_id = FVarId::new(2);
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let false_ty = Expr::const_(Name::from_string("False"), vec![]);

    ProofState::with_context(
        Environment::with_prelude(),
        false_ty,
        vec![
            LocalDecl {
                fvar: x_id,
                name: "x".into(),
                ty: nat_ty,
                value: None,
            },
            LocalDecl {
                fvar: hc_id,
                name: "hc".into(),
                ty: make_nat_le_tc(Expr::nat_lit(0), Expr::nat_lit(3)),
                value: None,
            },
            LocalDecl {
                fvar: hx_id,
                name: "hx".into(),
                ty: make_nat_le_tc(
                    Expr::nat_lit(1),
                    nat_add(Expr::fvar(x_id), Expr::nat_lit(2)),
                ),
                value: None,
            },
        ],
    )
}

fn assert_nlinarith_closed_proof_chain(state: &ProofState, check_ctx: clean_kernel::LocalContext) {
    let _ = state
        .proof_term()
        .expect("completed nlinarith state should preserve proof_term() extraction");
    let closed_proof = state
        .closed_proof()
        .expect("completed nlinarith state should preserve closed_proof() extraction");
    let goal_ty = state
        .goal_type()
        .expect("completed nlinarith state should retain the original goal type");
    let tc = TypeChecker::with_context(state.env(), check_ctx);
    assert!(
        tc.check_type(&closed_proof, &goal_ty).is_ok(),
        "nlinarith closed proof must type-check against the original goal type"
    );
}

#[test]
fn test_build_certified_nlinarith_proof_reconstructs_false_proof() {
    let state = contradictory_nat_le_false_state();
    let goal = state.current_goal().expect("should have a goal").clone();
    let proof = build_certified_nlinarith_proof(&state, &goal, &NlinarithConfig::default()).expect(
        "certified nlinarith helper should reconstruct a contradiction proof before decide",
    );

    let mut check_state = contradictory_nat_le_false_state();
    let check_goal = check_state
        .current_goal()
        .expect("fresh state should have the same False goal")
        .clone();
    check_state
        .close_goal(&check_goal, proof)
        .expect("certified nlinarith replay proof should pass kernel type-checking");
    assert!(
        check_state.is_complete(),
        "helper-produced proof should close the goal directly"
    );
}

#[test]
fn test_build_synthetic_row_decls_create_proof_carrying_scaled_local() {
    let mut state = synthetic_row_source_state();
    let goal = state.current_goal().expect("should have a goal").clone();
    let synthetic_rows = build_synthetic_row_decls(&mut state, &goal, &NlinarithConfig::default());

    assert_eq!(
        synthetic_rows.len(),
        1,
        "one constant-times-row synthetic hypothesis should be generated"
    );

    let synthetic_row = &synthetic_rows[0];
    let inferred_ty = state
        .infer_type(&goal, &synthetic_row.proof_value)
        .expect("synthetic row proof should infer inside the original goal context");
    assert!(
        state.is_def_eq(&goal, &inferred_ty, &synthetic_row.decl.ty),
        "stored synthetic row type should stay definitionally equal to the theorem-backed proof type"
    );
    assert!(
        match_le(&synthetic_row.decl.ty).is_some(),
        "synthetic row proof should materialize as a replayable <= hypothesis"
    );

    let check_ctx = synthetic_row_source_state()
        .current_goal()
        .expect("fresh state should have a goal")
        .local_ctx
        .clone();
    let mut check_state = ProofState::with_context(
        Environment::with_prelude(),
        synthetic_row.decl.ty.clone(),
        check_ctx,
    );
    let check_goal = check_state
        .current_goal()
        .expect("proof goal should exist")
        .clone();
    check_state
        .close_goal(&check_goal, synthetic_row.proof_value.clone())
        .expect("synthetic row proof should pass kernel type-checking against its stored type");
}

#[test]
fn test_build_synthetic_row_decls_scale_affine_local() {
    let mut state = affine_synthetic_row_source_state();
    let goal = state.current_goal().expect("should have a goal").clone();
    let synthetic_rows = build_synthetic_row_decls(&mut state, &goal, &NlinarithConfig::default());

    assert_eq!(
        synthetic_rows.len(),
        1,
        "a constant row should scale an affine <= row into one synthetic hypothesis"
    );

    let expected_ty = make_nat_le_tc(
        nat_mul(Expr::nat_lit(3), Expr::nat_lit(1)),
        nat_mul(
            Expr::nat_lit(3),
            nat_add(Expr::fvar(FVarId::new(0)), Expr::nat_lit(2)),
        ),
    );
    assert!(
        state.is_def_eq(&goal, &synthetic_rows[0].decl.ty, &expected_ty),
        "synthetic row should scale the full affine hypothesis, not just pure-variable rows"
    );
}

#[test]
fn test_build_certified_nlinarith_proof_rewrites_negated_goal_row() {
    let state = goal_derived_synthetic_row_state();
    let goal = state.current_goal().expect("should have a goal").clone();
    let proof = build_certified_nlinarith_proof(&state, &goal, &NlinarithConfig::default())
        .expect("certified replay should use the negated goal row as a proof-bearing local");

    let mut check_state = goal_derived_synthetic_row_state();
    let check_goal = check_state
        .current_goal()
        .expect("fresh state should have the same goal")
        .clone();
    check_state
        .close_goal(&check_goal, proof)
        .expect("negated-goal replay proof should pass kernel type-checking");
    assert!(
        check_state.is_complete(),
        "negated-goal replay proof should close the original strict goal"
    );
}

#[test]
fn test_certified_nlinarith_replay_context_preserves_goal_row_scope() {
    let state = goal_derived_synthetic_row_state();
    let goal = state.current_goal().expect("should have a goal").clone();
    let (scratch_goal, replay_rows) =
        build_certified_nlinarith_replay_context(&state, &goal, &NlinarithConfig::default())
            .expect("strict Nat goal should build a scratch replay context");

    let replay_tys: Vec<Expr> = replay_rows.iter().map(|row| row.decl.ty.clone()).collect();
    assert!(
        replay_tys.iter().any(|ty| state.is_def_eq(
            &scratch_goal,
            ty,
            &make_nat_le_tc(Expr::fvar(FVarId::new(0)), Expr::nat_lit(0))
        )),
        "scratch replay context should materialize the negated goal as x <= 0"
    );
    assert!(
        replay_tys.iter().any(|ty| {
            state.is_def_eq(
                &scratch_goal,
                ty,
                &make_nat_le_tc(
                    nat_mul(Expr::nat_lit(2), Expr::fvar(FVarId::new(0))),
                    Expr::nat_lit(0),
                ),
            )
        }),
        "scratch replay context should add the scaled synthetic row from the negated goal"
    );
}

#[test]
#[serial]
fn test_nlinarith_with_config_certified_replay_avoids_trusted_arith() {
    reset_all_counters();
    let mut state = contradictory_nat_le_false_state();

    let axiom_before = axiom_snapshot();
    let result = nlinarith_with_config(&mut state, NlinarithConfig::default());

    assert!(
        result.is_ok(),
        "nlinarith_with_config should replay the certified FM contradiction, got: {result:?}"
    );
    assert!(
        state.is_complete(),
        "goal should be closed after nlinarith_with_config succeeds"
    );
    assert_no_trusted_axiom_usage(
        "nlinarith_with_config",
        "contradictory Nat inequality via certified FM replay",
        axiom_before,
    );

    let ledger = state.trust_ledger();
    assert_eq!(
        ledger.trusted_arith_count, 0,
        "certified nlinarith replay must not increment trustedArith"
    );
    assert_eq!(
        ledger.sorry_count, 0,
        "certified nlinarith replay must produce a real proof term"
    );
}

#[test]
#[serial]
fn test_nlinarith_entrypoint_preserves_proof_chain_without_trusted_axioms() {
    reset_all_counters();
    let mut state = contradictory_nat_le_false_state();
    state.fvar_base = state.next_fvar;
    let original_goal = state.current_goal().expect("should have a goal").clone();

    let axiom_before = axiom_snapshot();
    let result = nlinarith(&mut state);

    assert!(
        result.is_ok(),
        "nlinarith should replay the certified FM contradiction, got: {result:?}"
    );
    assert!(
        state.is_complete(),
        "goal should be closed after nlinarith succeeds"
    );
    assert_no_trusted_axiom_usage(
        "nlinarith",
        "contradictory Nat inequality via public certified replay",
        axiom_before,
    );

    let ledger = state.trust_ledger();
    assert_eq!(
        ledger.trusted_arith_count, 0,
        "public nlinarith replay must not increment trustedArith"
    );
    assert_eq!(
        ledger.trusted_ay_count, 0,
        "public nlinarith replay must not increment trustedAy"
    );
    assert_eq!(
        ledger.sorry_count, 0,
        "public nlinarith replay must preserve a real proof term"
    );

    let check_ctx = state.build_local_ctx(&original_goal);
    assert_nlinarith_closed_proof_chain(&state, check_ctx);
}

#[test]
#[serial]
fn test_nlinarith_with_config_goal_derived_synthetic_row_avoids_trusted_arith() {
    // Wave 100: tightened baseline calibration. The previous test conditionally
    // TRACE+return'd when the `max_products=0` baseline closed the goal anyway,
    // because in this fixture (`0 < x` from `1 ≤ 2*x`) the certified-replay
    // negated-goal row path closes the goal without needing the synthetic-row
    // product preprocessing. The certified path is independent of
    // `max_products` (it always runs at the head of `nlinarith_with_config`),
    // so a non-trivial-but-linear-tractable fixture like this one will close
    // through that path regardless of the product cap.
    //
    // The invariant the test actually cares about is: *however* the goal
    // closes (baseline or default), no trusted-arith axiom is consumed and a
    // real kernel-checked proof term is produced. The hard-assertion below
    // captures exactly that for both configurations.

    reset_all_counters();
    let no_products = NlinarithConfig {
        max_products: 0,
        ..NlinarithConfig::default()
    };
    let mut baseline_state = goal_derived_synthetic_row_state();
    let axiom_before_baseline = axiom_snapshot();
    let baseline = nlinarith_with_config(&mut baseline_state, no_products);
    let baseline_ledger = baseline_state.trust_ledger();
    if baseline.is_ok() {
        // Baseline closed via the certified replay path (which does not
        // depend on `max_products`). It MUST still be axiom-clean.
        assert!(
            baseline_state.is_complete(),
            "baseline Ok implies goal closure"
        );
        assert_no_trusted_axiom_usage(
            "nlinarith_with_config(max_products=0)",
            "baseline path on goal-derived synthetic row",
            axiom_before_baseline,
        );
        assert_eq!(
            baseline_ledger.trusted_arith_count, 0,
            "baseline closure must not consume trustedArith"
        );
        assert_eq!(
            baseline_ledger.trusted_ay_count, 0,
            "baseline closure must not consume trustedAy"
        );
        assert_eq!(
            baseline_ledger.sorry_count, 0,
            "baseline closure must produce a real proof term"
        );
    } else {
        // Baseline could not close — that's fine, default config below will.
        // Verify we did not silently increment any trusted axiom in the failure path.
        assert_eq!(
            baseline_ledger.trusted_arith_count, 0,
            "baseline failure path must not leak trustedArith increments"
        );
    }

    reset_all_counters();
    let mut state = goal_derived_synthetic_row_state();
    let axiom_before = axiom_snapshot();
    let result = nlinarith_with_config(&mut state, NlinarithConfig::default());

    assert!(
        result.is_ok(),
        "nlinarith_with_config should replay through the negated-goal synthetic row, got: {result:?}"
    );
    assert!(
        state.is_complete(),
        "goal should be closed after the goal-derived synthetic-row replay succeeds"
    );
    assert_no_trusted_axiom_usage(
        "nlinarith_with_config",
        "strict Nat goal via goal-derived synthetic row replay",
        axiom_before,
    );

    let ledger = state.trust_ledger();
    assert_eq!(
        ledger.trusted_arith_count, 0,
        "goal-derived synthetic-row replay must not increment trustedArith"
    );
    assert_eq!(
        ledger.sorry_count, 0,
        "goal-derived synthetic-row replay must produce a real proof term"
    );
}

/// Negative calibration: a deliberately under-constrained variant of the
/// goal-derived synthetic-row state should NOT close with `nlinarith` — and
/// when it fails to close, it must do so without consuming any trusted
/// axioms. Removing the `1 ≤ 2*x` hypothesis (the key witness that makes
/// `0 < x` derivable) leaves the goal genuinely unprovable from context.
#[test]
#[serial]
fn test_nlinarith_with_config_without_witness_fails_closed_without_trusted_arith() {
    reset_all_counters();
    let x_id = FVarId::new(0);
    let hc_id = FVarId::new(1);
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let mut state = ProofState::with_context(
        Environment::with_prelude(),
        nat_lt_tc(Expr::nat_lit(0), Expr::fvar(x_id)),
        vec![
            LocalDecl {
                fvar: x_id,
                name: "x".into(),
                ty: nat_ty,
                value: None,
            },
            LocalDecl {
                fvar: hc_id,
                name: "hc".into(),
                ty: make_nat_le_tc(Expr::nat_lit(0), Expr::nat_lit(2)),
                value: None,
            },
            // Note: no `1 ≤ 2*x` hypothesis — the goal `0 < x` is unprovable.
        ],
    );

    let axiom_before = axiom_snapshot();
    let result = nlinarith_with_config(&mut state, NlinarithConfig::default());

    assert!(
        result.is_err(),
        "nlinarith must fail when the goal-supporting witness is removed; got: {result:?}"
    );
    assert!(
        !state.is_complete(),
        "an unsupported goal must remain open after nlinarith failure"
    );
    assert_no_trusted_axiom_usage(
        "nlinarith_with_config",
        "unsupported strict Nat goal (no `1 ≤ 2*x` witness)",
        axiom_before,
    );
    let ledger = state.trust_ledger();
    assert_eq!(
        ledger.trusted_arith_count, 0,
        "failure path must not increment trustedArith"
    );
    assert_eq!(
        ledger.trusted_ay_count, 0,
        "failure path must not increment trustedAy"
    );
    assert_eq!(ledger.sorry_count, 0, "failure path must not emit sorry");
}

#[test]
#[serial]
fn test_certified_nlinarith_outcome_distinguishes_no_certified_contradiction() {
    reset_all_counters();
    let mut state = synthetic_row_source_state();
    let goal = state.current_goal().expect("should have a goal").clone();
    let axiom_before = axiom_snapshot();
    let outcome = try_certified_nlinarith(&mut state, &goal, &NlinarithConfig::default());

    assert!(
        matches!(outcome, CertifiedNlinarithOutcome::NoCertifiedContradiction),
        "expected NoCertifiedContradiction on a satisfiable synthetic-row source state, got: {outcome:?}"
    );
    assert_eq!(
        axiom_snapshot(),
        axiom_before,
        "outcome probing must not emit trusted axioms"
    );
    let ledger = state.trust_ledger();
    assert_eq!(ledger.trusted_arith_count, 0);
    assert_eq!(ledger.trusted_ay_count, 0);
    assert_eq!(ledger.sorry_count, 0);
    assert!(
        !state.is_complete(),
        "outcome probing should leave the goal open on NoCertifiedContradiction"
    );
}

#[test]
#[serial]
fn test_certified_nlinarith_outcome_distinguishes_fail_closed_unsat() {
    reset_all_counters();
    let mut state = goal_derived_synthetic_row_state();
    let goal = state.current_goal().expect("should have a goal").clone();
    let axiom_before = axiom_snapshot();
    let outcome =
        force_certified_nlinarith_no_kernel_proof(&mut state, &goal, &NlinarithConfig::default());

    assert!(
        matches!(
            outcome,
            CertifiedNlinarithOutcome::CertifiedUnsatNoKernelProof { ref reason }
                if reason.contains("test-only forced fail-closed outcome")
        ),
        "expected CertifiedUnsatNoKernelProof on the forced negative seam, got: {outcome:?}"
    );
    assert_eq!(
        axiom_snapshot(),
        axiom_before,
        "forced fail-closed outcome must not emit trusted axioms"
    );
    let ledger = state.trust_ledger();
    assert_eq!(ledger.trusted_arith_count, 0);
    assert_eq!(ledger.trusted_ay_count, 0);
    assert_eq!(ledger.sorry_count, 0);
    assert!(
        !state.is_complete(),
        "forced fail-closed outcome should leave the goal open"
    );
}
