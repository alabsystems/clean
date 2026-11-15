// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for at-location tactics: rewrite_at, push_neg_at, simp_at, dsimp_at, unfold_at.
//!
//! Extracted from core.rs during #307 large file split.
//! These tests verify that at-location tactics modify hypotheses, not goals.
//! Before #1840, the elaborator silently discarded the location.

use super::*;
use clean_kernel::env::Declaration;

#[path = "at_location_push_neg_extra.rs"]
mod push_neg_extra;
#[path = "at_location_push_neg_wildcard.rs"]
mod push_neg_wildcard;
#[path = "at_location_simp_wildcard.rs"]
mod simp_wildcard;
#[path = "at_location_turnstile.rs"]
mod turnstile;

// ==========================================================================
// rewrite_at / push_neg_at — hypothesis location dispatch (#1840)
// ==========================================================================
// These tests verify that at-location tactics modify hypotheses, not goals.
// Before #1840, the elaborator silently discarded the location, always
// rewriting the goal.

#[test]
fn test_rewrite_at_modifies_hypothesis_not_goal() {
    // rw [h_eq] at h_target should rewrite h_target, leaving the goal unchanged
    let env = setup_env_with_full_eq();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);

    // Goal: P(x)
    // h_eq : x = y
    // h_target : P(x)
    let target = make_p(x.clone());
    let h_eq_ty = make_eq_n(x.clone(), y.clone());
    let h_target_ty = make_p(x.clone());

    let mut state = ProofState::with_context(
        env,
        target.clone(),
        vec![
            LocalDecl {
                binder_info: Default::default(),
                fvar: FVarId::new(0),
                name: clean_parser::SurfaceName::generated_path("h_eq"),
                ty: h_eq_ty,
                value: None,
            },
            LocalDecl {
                binder_info: Default::default(),
                fvar: FVarId::new(1),
                name: clean_parser::SurfaceName::generated_path("h_target"),
                ty: h_target_ty,
                value: None,
            },
        ],
    );

    // rewrite_at should rewrite h_target: P(x) → P(y)
    let result = rewrite_at(
        &mut state,
        &clean_parser::SurfaceName::generated_path("h_eq"),
        &clean_parser::SurfaceName::generated_path("h_target"),
        false,
    );
    assert!(result.is_ok(), "rewrite_at should succeed");

    let goal = state.current_goal().unwrap();
    // Goal should be UNCHANGED (still P(x))
    assert_eq!(
        goal.target, target,
        "goal should be unchanged after rw at hyp"
    );
    // h_target should be rewritten to P(y)
    let h_target = goal
        .local_ctx
        .iter()
        .find(|d| d.name == clean_parser::SurfaceName::generated_path("h_target"))
        .unwrap();
    assert_eq!(
        h_target.ty,
        make_p(y),
        "hypothesis should be rewritten to P(y)"
    );
}

#[test]
fn test_rewrite_at_reverse_direction() {
    // rw [← h_eq] at h_target should rewrite rhs → lhs in h_target
    let env = setup_env_with_full_eq();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);

    // Goal: P(x)
    // h_eq : x = y
    // h_target : P(y)  ← contains y, reverse rewrites y → x
    let target = make_p(x.clone());
    let h_eq_ty = make_eq_n(x.clone(), y.clone());
    let h_target_ty = make_p(y.clone());

    let mut state = ProofState::with_context(
        env,
        target.clone(),
        vec![
            LocalDecl {
                binder_info: Default::default(),
                fvar: FVarId::new(0),
                name: clean_parser::SurfaceName::generated_path("h_eq"),
                ty: h_eq_ty,
                value: None,
            },
            LocalDecl {
                binder_info: Default::default(),
                fvar: FVarId::new(1),
                name: clean_parser::SurfaceName::generated_path("h_target"),
                ty: h_target_ty,
                value: None,
            },
        ],
    );

    // rw [← h_eq] at h_target: P(y) → P(x)
    let result = rewrite_at(
        &mut state,
        &clean_parser::SurfaceName::generated_path("h_eq"),
        &clean_parser::SurfaceName::generated_path("h_target"),
        true,
    );
    assert!(result.is_ok(), "rewrite_at reverse should succeed");

    let goal = state.current_goal().unwrap();
    assert_eq!(goal.target, target, "goal should be unchanged");
    let h_target = goal
        .local_ctx
        .iter()
        .find(|d| d.name == clean_parser::SurfaceName::generated_path("h_target"))
        .unwrap();
    assert_eq!(
        h_target.ty,
        make_p(x),
        "hypothesis should be rewritten to P(x)"
    );
}

#[test]
fn test_rewrite_at_fails_when_pattern_not_in_hyp() {
    // rw [h_eq] at h_target should fail if the hypothesis doesn't contain the pattern
    let env = setup_env_with_full_eq();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let z = Expr::const_(Name::from_string("z"), vec![]);

    // h_eq : x = y, but h_target : P(z) — z is not x or y
    let target = make_p(z.clone());
    let h_eq_ty = make_eq_n(x, y);
    let h_target_ty = make_p(z);

    let mut state = ProofState::with_context(
        env,
        target,
        vec![
            LocalDecl {
                binder_info: Default::default(),
                fvar: FVarId::new(0),
                name: clean_parser::SurfaceName::generated_path("h_eq"),
                ty: h_eq_ty,
                value: None,
            },
            LocalDecl {
                binder_info: Default::default(),
                fvar: FVarId::new(1),
                name: clean_parser::SurfaceName::generated_path("h_target"),
                ty: h_target_ty,
                value: None,
            },
        ],
    );

    let result = rewrite_at(
        &mut state,
        &clean_parser::SurfaceName::generated_path("h_eq"),
        &clean_parser::SurfaceName::generated_path("h_target"),
        false,
    );
    assert!(
        result.is_err(),
        "rewrite_at should fail when pattern not in hypothesis"
    );
}

#[test]
fn test_rewrite_at_missing_target_hyp() {
    let env = setup_env_with_full_eq();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);

    let target = make_p(x.clone());
    let h_eq_ty = make_eq_n(x, y);

    let mut state = ProofState::with_context(
        env,
        target,
        vec![LocalDecl {
            binder_info: Default::default(),
            fvar: FVarId::new(0),
            name: clean_parser::SurfaceName::generated_path("h_eq"),
            ty: h_eq_ty,
            value: None,
        }],
    );

    // Target hypothesis "nonexistent" doesn't exist
    let result = rewrite_at(
        &mut state,
        &clean_parser::SurfaceName::generated_path("h_eq"),
        &clean_parser::SurfaceName::generated_path("nonexistent"),
        false,
    );
    assert!(
        matches!(result, Err(TacticError::HypothesisNotFound(ref s)) if s == "nonexistent"),
        "should report missing hypothesis"
    );
}

#[test]
fn test_push_neg_at_modifies_hypothesis_not_goal() {
    // push_neg at h should negate inside h, leaving the goal unchanged.
    // Uses proof-carrying replacement via replace_local_decl_with_cast,
    // so the environment must include classical logic + propext.
    let mut env = setup_env_with_prop_ext();

    let p = Expr::const_(Name::from_string("A"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    let not_not_p = make_not(&make_not(&p));

    // Goal: A
    // h : ¬¬A
    let target = p.clone();
    let mut state = ProofState::with_context(
        env,
        target.clone(),
        vec![LocalDecl {
            binder_info: Default::default(),
            fvar: FVarId::new(0),
            name: clean_parser::SurfaceName::generated_path("h"),
            ty: not_not_p,
            value: None,
        }],
    );

    let result = push_neg_at(&mut state, &clean_parser::SurfaceName::generated_path("h"));
    assert!(result.is_ok(), "push_neg_at should succeed: {result:?}");

    let goal = state.current_goal().unwrap();
    // Goal should be unchanged
    assert_eq!(
        goal.target, target,
        "goal should be unchanged after push_neg at h"
    );
    // h should be simplified from ¬¬A to A
    let h = goal
        .local_ctx
        .iter()
        .find(|d| d.name == clean_parser::SurfaceName::generated_path("h"))
        .unwrap();
    assert_eq!(
        h.ty, p,
        "push_neg_at should simplify ¬¬A to A in hypothesis"
    );
}

#[test]
fn test_simp_at_modifies_hypothesis_not_goal() {
    // simp at h should simplify h via beta reduction, leaving the goal unchanged
    let mut env = setup_env();
    env.init_eq().unwrap();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    // h : (λ x : A => x) a = a  (beta-reducible to a = a)
    // Goal: A
    let identity = Expr::lam(BinderInfo::Default, a_ty.clone(), Expr::bvar(0));
    let lhs = Expr::app(identity, a.clone());
    let h_ty = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                a_ty.clone(),
            ),
            lhs,
        ),
        a.clone(),
    );

    let target = a_ty.clone();
    let mut state = ProofState::with_context(
        env,
        target.clone(),
        vec![LocalDecl {
            binder_info: Default::default(),
            fvar: FVarId::new(0),
            name: clean_parser::SurfaceName::generated_path("h"),
            ty: h_ty,
            value: None,
        }],
    );

    let result = simp_at(&mut state, &clean_parser::SurfaceName::generated_path("h"));
    assert!(result.is_ok(), "simp_at should succeed: {result:?}");

    let goal = state.current_goal().unwrap();
    // Goal should be unchanged
    assert_eq!(
        goal.target, target,
        "goal should be unchanged after simp at h"
    );
    // h should have been simplified (beta reduction applied)
    let h = goal
        .local_ctx
        .iter()
        .find(|d| d.name == clean_parser::SurfaceName::generated_path("h"))
        .unwrap();
    assert_ne!(
        h.ty,
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                    a_ty,
                ),
                Expr::app(
                    Expr::lam(
                        BinderInfo::Default,
                        Expr::const_(Name::from_string("A"), vec![]),
                        Expr::bvar(0),
                    ),
                    a,
                ),
            ),
            Expr::const_(Name::from_string("a"), vec![]),
        ),
        "simp_at should have simplified hypothesis h"
    );
}

#[test]
fn test_simp_at_fails_on_missing_hypothesis() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    let result = simp_at(
        &mut state,
        &clean_parser::SurfaceName::generated_path("nonexistent"),
    );
    assert!(
        matches!(result, Err(TacticError::HypothesisNotFound(ref s)) if s == "nonexistent"),
        "simp_at should report missing hypothesis"
    );
}

#[test]
fn test_dsimp_at_beta_reduces_hypothesis() {
    // dsimp at h should beta-reduce (λ x => P x) a to P a in hypothesis h
    let mut env = setup_env();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            Expr::const_(Name::from_string("A"), vec![]),
            Expr::type_(),
        ),
    })
    .unwrap();

    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let p = Expr::const_(Name::from_string("P"), vec![]);

    // h : (λ x : A => P x) a   — beta-reducible to P a
    let family = Expr::lam(
        BinderInfo::Default,
        a_ty.clone(),
        Expr::app(p.clone(), Expr::bvar(0)),
    );
    let h_ty = Expr::app(family, a.clone());

    // Goal: B
    let target = Expr::const_(Name::from_string("B"), vec![]);
    let mut state = ProofState::with_context(
        env,
        target.clone(),
        vec![LocalDecl {
            binder_info: Default::default(),
            fvar: FVarId::new(0),
            name: clean_parser::SurfaceName::generated_path("h"),
            ty: h_ty,
            value: None,
        }],
    );

    let result = dsimp_at(&mut state, &clean_parser::SurfaceName::generated_path("h"));
    assert!(result.is_ok(), "dsimp_at should succeed: {result:?}");

    let goal = state.current_goal().unwrap();
    // Goal should be unchanged
    assert_eq!(
        goal.target, target,
        "goal should be unchanged after dsimp at h"
    );
    // h should now be beta-reduced to `P a`
    let h = goal
        .local_ctx
        .iter()
        .find(|d| d.name == clean_parser::SurfaceName::generated_path("h"))
        .unwrap();
    assert_eq!(
        h.ty,
        Expr::app(p, a),
        "dsimp_at should beta-reduce hypothesis to `P a`"
    );
}

#[test]
fn test_unfold_at_expands_definition_in_hypothesis() {
    // unfold mydef at h should expand mydef in hypothesis h
    let mut env = setup_env();

    // Define: mydef := a
    let a = Expr::const_(Name::from_string("a"), vec![]);
    env.add_decl(Declaration::Definition {
        name: Name::from_string("mydef"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("A"), vec![]),
        value: a.clone(),
        is_reducible: true,
    })
    .unwrap();

    // h : P(mydef)  where P : A → Prop
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            Expr::const_(Name::from_string("A"), vec![]),
            Expr::prop(),
        ),
    })
    .unwrap();

    let mydef = Expr::const_(Name::from_string("mydef"), vec![]);
    let h_ty = Expr::app(Expr::const_(Name::from_string("P"), vec![]), mydef);

    // Goal: B
    let target = Expr::const_(Name::from_string("B"), vec![]);
    let mut state = ProofState::with_context(
        env,
        target.clone(),
        vec![LocalDecl {
            binder_info: Default::default(),
            fvar: FVarId::new(0),
            name: clean_parser::SurfaceName::generated_path("h"),
            ty: h_ty,
            value: None,
        }],
    );

    let result = unfold_at(
        &mut state,
        &clean_parser::SurfaceName::generated_path("mydef"),
        &clean_parser::SurfaceName::generated_path("h"),
    );
    assert!(result.is_ok(), "unfold_at should succeed: {result:?}");

    let goal = state.current_goal().unwrap();
    // Goal should be unchanged
    assert_eq!(
        goal.target, target,
        "goal should be unchanged after unfold at h"
    );
    // h should now be P(a) instead of P(mydef)
    let h = goal
        .local_ctx
        .iter()
        .find(|d| d.name == clean_parser::SurfaceName::generated_path("h"))
        .unwrap();
    let expected_ty = Expr::app(Expr::const_(Name::from_string("P"), vec![]), a);
    assert_eq!(
        h.ty, expected_ty,
        "unfold_at should expand mydef to a in hypothesis"
    );
}

#[test]
fn test_unfold_at_fails_on_missing_hypothesis() {
    let mut env = setup_env();
    env.add_decl(Declaration::Definition {
        name: Name::from_string("mydef"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("A"), vec![]),
        value: Expr::const_(Name::from_string("a"), vec![]),
        is_reducible: true,
    })
    .unwrap();

    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    let result = unfold_at(
        &mut state,
        &clean_parser::SurfaceName::generated_path("mydef"),
        &clean_parser::SurfaceName::generated_path("nonexistent"),
    );
    assert!(
        matches!(result, Err(TacticError::HypothesisNotFound(ref s)) if s == "nonexistent"),
        "unfold_at should report missing hypothesis"
    );
}

#[test]
fn test_unfold_at_fails_when_def_not_in_hyp() {
    // unfold mydef at h should fail when mydef does not appear in h
    let mut env = setup_env();

    let a = Expr::const_(Name::from_string("a"), vec![]);
    env.add_decl(Declaration::Definition {
        name: Name::from_string("mydef"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("A"), vec![]),
        value: a.clone(),
        is_reducible: true,
    })
    .unwrap();

    // h : A  (does not contain mydef)
    let target = Expr::const_(Name::from_string("B"), vec![]);
    let mut state = ProofState::with_context(
        env,
        target,
        vec![LocalDecl {
            binder_info: Default::default(),
            fvar: FVarId::new(0),
            name: clean_parser::SurfaceName::generated_path("h"),
            ty: Expr::const_(Name::from_string("A"), vec![]),
            value: None,
        }],
    );

    let result = unfold_at(
        &mut state,
        &clean_parser::SurfaceName::generated_path("mydef"),
        &clean_parser::SurfaceName::generated_path("h"),
    );
    assert!(
        result.is_err(),
        "unfold_at should fail when definition not in hypothesis"
    );
}

#[test]
fn test_simp_rw_wildcard_passes_lemma_names_to_hypotheses() {
    // Regression test: simp_rw [...] at * must pass the user's lemma names
    // to each hypothesis via simp_only_at, not call generic simp_all.
    // This verifies the fix for the Wildcard branch in elab_tactic.rs
    // that previously dropped the `names` vector (Re: #1840).
    //
    // The hypothesis type must be a Prop so that Eq.subst's identity motive
    // (λ T : Prop, T) type-checks. Non-Prop types like `a : A` produce
    // ill-typed motive (λ T : A, T) that close_goal correctly rejects.
    let mut env = setup_env();
    env.init_eq().unwrap();

    // Add a proposition for the hypothesis type
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    let p = Expr::const_(Name::from_string("P"), vec![]);

    // h : (λ Q : Prop, Q) P  — beta-reducible to `P`
    let identity = Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
    let h_ty = Expr::app(identity, p.clone());

    // Goal: B (unrelated, should survive)
    let target = Expr::const_(Name::from_string("B"), vec![]);
    let mut state = ProofState::with_context(
        env,
        target.clone(),
        vec![LocalDecl {
            binder_info: Default::default(),
            fvar: FVarId::new(0),
            name: clean_parser::SurfaceName::generated_path("h"),
            ty: h_ty.clone(),
            value: None,
        }],
    );

    // Simulate simp_rw [...] at * Wildcard dispatch:
    // 1. Apply simp_only_at to each hypothesis with lemma names
    // 2. Apply simp_rw to goal
    let names = vec![clean_parser::SurfaceName::generated_path("some_lemma")];
    let hyp_result = simp_only_at(
        &mut state,
        &clean_parser::SurfaceName::generated_path("h"),
        names.clone(),
    );
    // simp_only_at must succeed: the hypothesis (λ Q : Prop, Q) P is beta-reducible to P
    assert!(
        hyp_result.is_ok(),
        "simp_only_at should beta-reduce hypothesis, got: {hyp_result:?}"
    );
    let goal = state.current_goal().unwrap();
    let h = goal
        .local_ctx
        .iter()
        .find(|d| d.name == clean_parser::SurfaceName::generated_path("h"))
        .unwrap();
    assert_ne!(
        h.ty, h_ty,
        "simp_only_at with names should still beta-reduce hypothesis"
    );

    // Goal should be unchanged (B is not simplifiable)
    let goal = state.current_goal().unwrap();
    assert_eq!(
        goal.target, target,
        "goal should be unchanged when not simplifiable"
    );
}

#[path = "at_location_proof_terms.rs"]
mod proof_terms;
