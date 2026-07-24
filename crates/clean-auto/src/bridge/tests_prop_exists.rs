// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for existential witness reconstruction helpers.
//!
//! Covers `goal_scoped_witness_candidates`, `build_exists_proof`,
//! `try_exists_elim`, and related bridge APIs accessible at `pub(super)`.
//!
//! Part of #2902 Wave A.

use super::super::proof_translation_contract::{classify_for_proof_translation, SmtLogicalForm};
use super::*;
use clean_kernel::Level;

fn mk_const(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

#[test]
fn test_goal_scoped_witness_candidates_finds_env_constants() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    // setup_env declares a, b, c : A, which are closed monomorphic constants
    // that goal_scoped_witness_candidates can discover.
    let a_ty = mk_const("A");
    let candidates = bridge.goal_scoped_witness_candidates(&a_ty);
    assert!(
        !candidates.is_empty(),
        "should find env constants a/b/c as witness candidates for type A"
    );
}

#[test]
fn test_goal_scoped_witness_candidates_empty_for_unknown_type() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let unknown_ty = mk_const("UnknownType");
    let candidates = bridge.goal_scoped_witness_candidates(&unknown_ty);
    assert!(
        candidates.is_empty(),
        "should have no candidates for undeclared type"
    );
}

#[test]
fn test_build_exists_proof_fails_without_witness() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let a_ty = mk_const("A");
    let body = Expr::bvar(0); // ∃ x : A, x — no witness available
    let goal = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Exists"), vec![Level::zero()]),
            a_ty.clone(),
        ),
        Expr::lam(
            clean_kernel::BinderInfo::Default,
            a_ty.clone(),
            body.clone(),
        ),
    );

    let result = bridge.build_exists_proof(&goal, &a_ty, &body, 0);
    assert!(
        result.is_err(),
        "build_exists_proof should fail without witnesses"
    );
}

#[test]
fn test_try_exists_elim_fails_without_hypotheses() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let goal_expr = mk_const("False");
    let goal_class = bridge.classify_prop(&goal_expr);
    let result = bridge.try_exists_elim(&goal_class, &goal_expr, 0);
    assert!(
        result.is_err(),
        "try_exists_elim should fail without existential hypotheses"
    );
}

#[test]
fn test_extract_exists_universe_from_well_formed_exists() {
    // The universe extraction is tested indirectly through the classifier:
    // classify_for_proof_translation on an Exists expression should succeed
    // and return the correct binder type.
    let nat_ty = mk_const("Nat");
    let body = Expr::bvar(0);
    let exists_expr = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Exists"), vec![Level::zero()]),
            nat_ty.clone(),
        ),
        Expr::lam(clean_kernel::BinderInfo::Default, nat_ty, body),
    );

    let form = classify_for_proof_translation(&exists_expr);
    assert!(
        matches!(form, SmtLogicalForm::Exists { .. }),
        "well-formed Exists should classify correctly, got {form:?}"
    );
}

#[test]
fn test_mk_exists_intro_term_requires_valid_universe() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let a_ty = mk_const("A");
    let body = Expr::bvar(0);
    let witness = mk_const("a");
    let body_proof = mk_const("body_proof_placeholder");

    // mk_exists_intro_term calls sort_level_of_type("A") which needs A in env
    let result = bridge.mk_exists_intro_term(None, &a_ty, &body, &witness, &body_proof);
    assert!(
        result.is_ok(),
        "mk_exists_intro_term should succeed when binder type is in env: {result:?}"
    );
}

#[test]
fn test_mk_exists_intro_term_fails_for_unknown_type() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let unknown_ty = mk_const("UnknownType");
    let body = Expr::bvar(0);
    let witness = mk_const("w");
    let body_proof = mk_const("pf");

    let result = bridge.mk_exists_intro_term(None, &unknown_ty, &body, &witness, &body_proof);
    assert!(
        result.is_err(),
        "mk_exists_intro_term should fail when binder type is not in env"
    );
}

#[test]
fn test_mk_exists_elim_term_requires_valid_universe() {
    let env = setup_env();
    let bridge = SmtBridge::new(&env);

    let a_ty = mk_const("A");
    let body = Expr::bvar(0);
    let goal = mk_const("False");
    let hyp = mk_const("h");
    let continuation = mk_const("k");

    let result = bridge.mk_exists_elim_term(None, &a_ty, &body, &goal, &hyp, &continuation);
    assert!(
        result.is_ok(),
        "mk_exists_elim_term should succeed with declared binder type: {result:?}"
    );
}
