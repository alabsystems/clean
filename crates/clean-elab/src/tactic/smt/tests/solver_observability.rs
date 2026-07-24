// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use serial_test::serial;

// ============================================================================
// SmtSolver::prove direct-proof observability tests (Part of #302)
// ============================================================================
//
// These tests check the SmtSolver API surface around the optional direct ay
// proof, so we can tell whether the Alethe reconstruction path produced a
// kernel proof term or the tactic would need the trust-free bridge fallback
// instead.

/// SmtSolver::prove returns a direct kernel proof for h:P, h:¬P contradiction.
///
/// The backend proof reconstruction already handles this live ay proof shape.
/// `SmtSolver::prove` should preserve that by not injecting the trivial `¬False`
/// assertion that only perturbs the solver proof DAG.
#[cfg(feature = "ay-smt")]
#[test]
#[serial]
fn test_smt_solver_prove_exposes_direct_proof_status_on_contradiction() {
    use crate::tactic::LocalDecl;
    use crate::unify::MetaState;
    use clean_kernel::FVarId;

    // p is a Prop-typed proposition variable; h1 and h2 are hypothesis FVars
    let p_fvar = FVarId::new(10);
    let p_expr = Expr::fvar(p_fvar);
    let neg_p = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        p_expr.clone(),
    );
    let false_const = Expr::const_(Name::from_string("False"), vec![]);

    let h1_fvar = FVarId::new(1);
    let h2_fvar = FVarId::new(2);

    // Register proposition variable as Prop-typed local
    let local_ctx = vec![LocalDecl {
        fvar: p_fvar,
        name: "p".to_string(),
        ty: Expr::prop(),
        value: None,
    }];

    let config = AyConfig::default().with_verify_policy(SmtVerifyPolicy::ExtractOnly);

    let mut solver =
        SmtSolver::from_config(&config, clean_auto::bridge::ay_contract::AyLogic::QfUf);

    // Register proposition FVar so translator can map it
    let metas = MetaState::new();
    solver
        .register_fvars_from_context(&local_ctx, &metas)
        .expect("Prop-typed local should register");

    // Assert hypotheses: h1 proves p, h2 proves ¬p
    solver
        .translate_and_assert_hypothesis(h1_fvar, &p_expr)
        .expect("should translate p");
    solver
        .translate_and_assert_hypothesis(h2_fvar, &neg_p)
        .expect("should translate ¬p");

    reset_local_ay_reconstruction_success_counter();
    let outcome = solver
        .prove(&false_const)
        .expect("SmtSolver::prove should succeed on contradiction");

    assert!(outcome.proved, "h:P, h:¬P should make ¬False UNSAT");
    assert!(
        outcome.direct_proof().is_some(),
        "direct ay contradiction should produce a reusable kernel proof"
    );
    assert_eq!(
        outcome.direct_trust_subterm_count(),
        Some(0),
        "simple contradiction should stay fully reconstructed"
    );
    assert_eq!(
        outcome.solver_verification(),
        None,
        "verifiable proof extraction path should not fabricate fast-path solve metadata"
    );

    let recon_count = local_ay_reconstruction_success_count();
    assert!(
        recon_count >= 1,
        "direct_proof().is_some() implies reconstruction counter should have incremented; \
         got {recon_count}"
    );
}

/// TrustSolver mode proves via ay but exposes no direct proof/trust debt.
///
/// This keeps the API honest: a fast-path UNSAT result should not masquerade
/// as a zero-trust reconstructed proof when the tactic still needs the bridge
/// or shared fail-closed recovery lane to produce a kernel term.
#[cfg(feature = "ay-smt")]
#[test]
#[serial]
fn test_smt_solver_prove_trust_solver_exposes_no_direct_proof() {
    let truth = Expr::const_(Name::from_string("True"), vec![]);
    let neg_truth = Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        truth.clone(),
    );
    let false_const = Expr::const_(Name::from_string("False"), vec![]);

    let mut solver = SmtSolver::from_config(
        &AyConfig::default(),
        clean_auto::bridge::ay_contract::AyLogic::QfUf,
    );

    solver
        .translate_and_assert(&truth)
        .expect("should translate True");
    solver
        .translate_and_assert(&neg_truth)
        .expect("should translate ¬True");

    reset_local_ay_reconstruction_success_counter();
    let outcome = solver
        .prove(&false_const)
        .expect("TrustSolver should still report UNSAT on contradiction");

    assert!(outcome.proved, "True and ¬True should make ¬False UNSAT");
    assert!(
        outcome.direct_proof().is_none(),
        "TrustSolver should not expose a direct kernel proof"
    );
    assert_eq!(
        outcome.direct_trust_subterm_count(),
        None,
        "without a direct proof there is no exact direct-proof trust debt to report"
    );
    let verification = outcome
        .solver_verification()
        .expect("TrustSolver should preserve fast-path solve verification metadata");
    assert!(
        !verification.summary.sat_model_validated,
        "UNSAT contradiction should not claim SAT model validation"
    );
    assert!(
        !verification.summary.unsat_proof_available,
        "fast backend should not claim a proof artifact on the trusted path"
    );
    assert_eq!(
        local_ay_reconstruction_success_count(),
        0,
        "fast-path proving must not increment the direct reconstruction counter"
    );
}
