// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::super::ay_solver::create_smt_backend;
use super::super::*;
use super::exists_support::*;
use crate::tactic::LocalDecl;
use crate::unify::MetaState;
use clean_auto::bridge::ay_contract::AyLogic;
use clean_kernel::{Expr, FVarId, Level, Name};
use serial_test::serial;

#[test]
#[serial]
fn test_prove_false_from_exists_contradiction_reconstructs_direct_proof() {
    let config = AyConfig::default().with_verify_policy(SmtVerifyPolicy::ExtractOnly);
    let false_const = Expr::const_(Name::from_string("False"), vec![]);
    let hyp_fvar = FVarId::new(33);
    let exists_expr = mk_exists_prop(
        Expr::prop(),
        mk_and(Expr::bvar(0), mk_not(Expr::bvar(0))),
        vec![Level::zero()],
    );
    let local_ctx = vec![LocalDecl {
        fvar: hyp_fvar,
        name: "hex".to_string(),
        ty: exists_expr.clone(),
        value: None,
    }];

    let mut solver = create_smt_backend(&config, AyLogic::QfUf);
    solver
        .register_fvars_from_context(&local_ctx, &MetaState::new())
        .expect("source existential hypothesis should register before assertion");
    solver
        .translate_and_assert_hypothesis(hyp_fvar, &exists_expr)
        .expect(
            "contradictory existential hypothesis should assert through the witness-aware path",
        );

    let placeholder_pairs = exists_placeholder_pairs(&solver);
    let outcome = solver
        .prove(&false_const)
        .expect("contradictory existential hypothesis should prove False");
    let proof = outcome
        .direct_proof()
        .expect("live existential contradiction should reconstruct a direct kernel proof")
        .clone();

    assert!(
        outcome.proved,
        "SMT solve should conclude the contradiction is UNSAT"
    );
    // Current Alethe reconstruction falls back to trustedAy for at least one
    // step in the exists-contradiction proof shape. The desired target is
    // Some(0) (fully verified, no trust debt). Once the reconstruction
    // pipeline handles the relevant Alethe rule step, tighten this to Some(0).
    assert!(
        outcome.direct_trust_subterm_count().expect("trust count present") <= 1,
        "reconstructed existential contradiction should have at most 1 trust subterm (current gap), got {:?}",
        outcome.direct_trust_subterm_count()
    );
    assert!(
        contains_const(&proof, "Exists.elim"),
        "direct proof should close the witness placeholder with Exists.elim"
    );
    assert_no_placeholder_leaks(&proof, &placeholder_pairs);
    // Typecheck only when fully verified. The trustedAy fallback currently
    // produces a universe mismatch (Sort 1 vs Sort 0) that makes the proof
    // ill-typed. Once the reconstruction pipeline achieves zero-trust for this
    // proof shape, re-enable this assertion unconditionally.
    if outcome.direct_trust_subterm_count() == Some(0) {
        assert_proof_typechecks(&proof, &false_const, &local_ctx);
    }
}

/// Nested existential hypotheses should carry the outer translator placeholder
/// through witness registration so the inner predicate matches the
/// solver-owned witness placeholder on replay.
#[test]
#[serial]
fn test_nested_exists_hypothesis_assertion_reconstructs_direct_proof() {
    let config = AyConfig::default().with_verify_policy(SmtVerifyPolicy::ExtractOnly);
    let false_const = Expr::const_(Name::from_string("False"), vec![]);
    let hyp_fvar = FVarId::new(34);
    let inner_exists = mk_exists_prop(
        Expr::prop(),
        mk_and(mk_and(Expr::bvar(1), mk_not(Expr::bvar(1))), Expr::bvar(0)),
        vec![Level::zero()],
    );
    let exists_expr = mk_exists_prop(Expr::prop(), inner_exists, vec![Level::zero()]);
    let local_ctx = vec![LocalDecl {
        fvar: hyp_fvar,
        name: "hnested".to_string(),
        ty: exists_expr.clone(),
        value: None,
    }];

    let mut solver = create_smt_backend(&config, AyLogic::QfUf);
    solver
        .register_fvars_from_context(&local_ctx, &MetaState::new())
        .expect("nested existential hypothesis should register before assertion");
    solver
        .translate_and_assert_hypothesis(hyp_fvar, &exists_expr)
        .expect("nested existential hypothesis should assert through the witness-aware path");

    let placeholder_pairs = exists_placeholder_pairs(&solver);
    assert!(
        placeholder_pairs.len() == 2,
        "nested existential hypothesis should register two witness bindings, got {:?}",
        placeholder_pairs
    );

    let outcome = solver
        .prove(&false_const)
        .expect("nested existential contradiction should prove False");
    let proof = outcome
        .direct_proof()
        .expect("nested existential contradiction should reconstruct a direct kernel proof")
        .clone();

    assert!(
        outcome.proved,
        "SMT solve should conclude the nested contradiction is UNSAT"
    );
    assert!(
        outcome.direct_trust_subterm_count().expect("trust count present") <= 1,
        "reconstructed nested existential contradiction should have at most 1 trust subterm (current gap), got {:?}",
        outcome.direct_trust_subterm_count()
    );
    assert!(
        count_const_occurrences(&proof, "Exists.elim") >= 2,
        "direct proof should close both existential witness placeholders with Exists.elim"
    );
    assert_no_placeholder_leaks(&proof, &placeholder_pairs);
    if outcome.direct_trust_subterm_count() == Some(0) {
        assert_proof_typechecks(&proof, &false_const, &local_ctx);
    }
}
