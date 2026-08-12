// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression coverage for conditional simp lemmas and their discharger (RC-J).
//!
//! Before this landed, a `@[simp]` lemma carrying a hypothesis
//! (`(a : N) (h : P a) : f a = a`) reached proof assembly with the hypothesis
//! slot missing: `extract_equality_full` recursed THROUGH the `Pi` binders and
//! dropped the premise, and the argument loop applied one argument per matched
//! pattern BVar only. The assembled term was `cond_lemma x` — still `Pi`-typed
//! — and the failure surfaced only at the kernel as
//! `TypeMismatch { expected: <the equality>, inferred: Pi(..) }`.
//!
//! Every test here asserts one of the two halves of the contract: a
//! dischargeable premise makes the rewrite fire *with a proof whose inferred
//! type is the rewritten equality*, and an undischargeable one abandons the
//! rewrite entirely (no rewrite, no proof, no fabricated witness).

use clean_kernel::env::{Declaration, SimpPriority};
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Environment, Expr, FVarId};

use super::{collect_simp_lemmas, simp_expr, SimpConfig};
use crate::tactic::core::{Goal, LocalDecl, ProofState};
use crate::tactic::tests::{make_eq_n, setup_env_with_full_eq};

// ============================================================================
// Fixtures
// ============================================================================

fn n_ty() -> Expr {
    Expr::const_(Name::from_string("N"), vec![])
}

fn const_(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

/// `P a` for the `P : N → Prop` predicate `setup_env_with_full_eq` registers.
fn p_of(arg: Expr) -> Expr {
    Expr::app(const_("P"), arg)
}

fn app1(head: &str, arg: Expr) -> Expr {
    Expr::app(const_(head), arg)
}

fn add_axiom(env: &mut Environment, name: &str, type_: Expr) {
    env.add_decl(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
    })
    .expect("test fixture axiom should register");
}

/// Register `f : N → N` (opaque, so nothing reduces by accident).
fn add_unary_fn(env: &mut Environment, name: &str) {
    add_axiom(env, name, Expr::pi(BinderInfo::Default, n_ty(), n_ty()));
}

/// Register `name : ∀ (a : N), <premise> → f a = a` and mark it `@[simp]`.
///
/// `premise` is written over `BVar 0` (the `a` binder), which is exactly how
/// the kernel stores the hypothesis' domain.
fn add_conditional_simp_lemma(env: &mut Environment, name: &str, fn_name: &str, premise: Expr) {
    let ty = Expr::pi(
        BinderInfo::Default,
        n_ty(),
        Expr::pi(
            BinderInfo::Default,
            premise,
            // One binder deeper now, so `a` reads as BVar 1.
            make_eq_n(app1(fn_name, Expr::bvar(1)), Expr::bvar(1)),
        ),
    );
    add_axiom(env, name, ty);
    env.register_simp_lemma(Name::from_string(name), SimpPriority::Default);
}

/// Register the UNCONDITIONAL `name : ∀ (a : N), g a = a` and mark it `@[simp]`.
fn add_unconditional_simp_lemma(env: &mut Environment, name: &str, fn_name: &str) {
    let ty = Expr::pi(
        BinderInfo::Default,
        n_ty(),
        make_eq_n(app1(fn_name, Expr::bvar(0)), Expr::bvar(0)),
    );
    add_axiom(env, name, ty);
    env.register_simp_lemma(Name::from_string(name), SimpPriority::Default);
}

/// A proof state whose single goal carries `hyps` (name, type) in its context.
fn state_with_hyps(env: Environment, hyps: &[(&str, Expr)]) -> ProofState {
    let ctx: Vec<LocalDecl> = hyps
        .iter()
        .enumerate()
        .map(|(index, (name, ty))| LocalDecl {
            fvar: FVarId::new(index as u64),
            name: (*name).to_string(),
            ty: ty.clone(),
            value: None,
        })
        .collect();
    // The target is irrelevant to `simp_expr`; the local context is what the
    // discharger reads.
    ProofState::with_context(env, make_eq_n(const_("x"), const_("x")), ctx)
}

fn goal_of(state: &ProofState) -> Goal {
    state
        .current_goal()
        .expect("fixture state should have a goal")
        .clone()
}

/// Assert that `proof` really witnesses `lhs = rhs`, checked in the goal's own
/// local context (the proof mentions hypothesis FVars, so a context-free kernel
/// check does not apply here).
fn assert_proves_rewrite(state: &ProofState, goal: &Goal, proof: &Expr, lhs: &Expr, rhs: &Expr) {
    let ty = state
        .infer_type(goal, proof)
        .expect("a discharged simp proof must have an inferable type");
    let expected = make_eq_n(lhs.clone(), rhs.clone());
    assert!(
        state.is_def_eq(goal, &ty, &expected),
        "assembled proof should prove the rewritten equality; inferred {ty:?}"
    );
}

// ============================================================================
// Positive: a premise a local hypothesis already proves
// ============================================================================

// RED without the fix: the rewrite fired, but the assembled proof was
// `f_id_of_p x` of type `P x → f x = x`, which `assert_proves_rewrite` (and,
// in the real pipeline, the kernel) rejects.
#[test]
fn test_simp_conditional_lemma_premise_in_context_rewrites_with_checked_proof() {
    let mut env = setup_env_with_full_eq();
    add_unary_fn(&mut env, "f");
    add_conditional_simp_lemma(&mut env, "f_id_of_p", "f", p_of(Expr::bvar(0)));

    let state = state_with_hyps(env, &[("h", p_of(const_("x")))]);
    let goal = goal_of(&state);
    let config = SimpConfig::new();
    let lemmas = collect_simp_lemmas(&state, &config);

    let target = app1("f", const_("x"));
    let result = simp_expr(&state, &goal, &target, &lemmas, &config);

    assert_eq!(
        result.expr,
        const_("x"),
        "with `h : P x` in context the conditional lemma must fire"
    );
    let proof = result
        .proof
        .as_ref()
        .expect("a conditional rewrite must carry a proof term");
    assert_proves_rewrite(&state, &goal, proof, &target, &const_("x"));
}

// RED without the fix: `f x` rewrote to `x` even with NO premise available,
// producing the `Pi`-typed proof the kernel later rejected.
#[test]
fn test_simp_conditional_lemma_premise_absent_does_not_rewrite() {
    let mut env = setup_env_with_full_eq();
    add_unary_fn(&mut env, "f");
    add_conditional_simp_lemma(&mut env, "f_id_of_p", "f", p_of(Expr::bvar(0)));

    // No `P x` hypothesis anywhere.
    let state = state_with_hyps(env, &[]);
    let goal = goal_of(&state);
    let config = SimpConfig::new();
    let lemmas = collect_simp_lemmas(&state, &config);

    let target = app1("f", const_("x"));
    let result = simp_expr(&state, &goal, &target, &lemmas, &config);

    assert_eq!(
        result.expr, target,
        "an undischargeable side condition must abandon the rewrite"
    );
    assert!(
        result.proof.is_none(),
        "no proof may be produced when nothing was rewritten"
    );
}

// The available premise is about the WRONG term: `h : P y` must not discharge
// `P x`.
#[test]
fn test_simp_conditional_lemma_premise_about_other_term_does_not_rewrite() {
    let mut env = setup_env_with_full_eq();
    add_unary_fn(&mut env, "f");
    add_conditional_simp_lemma(&mut env, "f_id_of_p", "f", p_of(Expr::bvar(0)));

    let state = state_with_hyps(env, &[("h", p_of(const_("y")))]);
    let goal = goal_of(&state);
    let config = SimpConfig::new();
    let lemmas = collect_simp_lemmas(&state, &config);

    let target = app1("f", const_("x"));
    let result = simp_expr(&state, &goal, &target, &lemmas, &config);

    assert_eq!(
        result.expr, target,
        "`P y` must not be accepted as a proof of `P x`"
    );
    assert!(result.proof.is_none());
}

// ============================================================================
// Negative: a premise that is FALSE
// ============================================================================

// A conditional lemma gated on `False` must never fire — there is no proof of
// `False` to discharge it with, and the discharger must not invent one.
#[test]
fn test_simp_conditional_lemma_false_premise_never_rewrites() {
    let mut env = setup_env_with_full_eq();
    add_axiom(&mut env, "False", Expr::prop());
    add_unary_fn(&mut env, "f");
    add_conditional_simp_lemma(&mut env, "f_id_of_false", "f", const_("False"));

    // Even with plenty of unrelated hypotheses in scope.
    let state = state_with_hyps(env, &[("h1", p_of(const_("x"))), ("h2", p_of(const_("y")))]);
    let goal = goal_of(&state);
    let config = SimpConfig::new();
    let lemmas = collect_simp_lemmas(&state, &config);

    let target = app1("f", const_("x"));
    let result = simp_expr(&state, &goal, &target, &lemmas, &config);

    assert_eq!(
        result.expr, target,
        "a lemma gated on `False` must never rewrite"
    );
    assert!(result.proof.is_none());
}

// ============================================================================
// Positive: a premise the trivial closers handle
// ============================================================================

// `(h : a = a) → f a = a` — the side condition is reflexive, so `Eq.refl`
// discharges it with no hypothesis in context at all.
#[test]
fn test_simp_conditional_lemma_reflexive_premise_discharged_by_rfl() {
    let mut env = setup_env_with_full_eq();
    add_unary_fn(&mut env, "f");
    let reflexive = make_eq_n(Expr::bvar(0), Expr::bvar(0));
    add_conditional_simp_lemma(&mut env, "f_id_of_refl", "f", reflexive);

    let state = state_with_hyps(env, &[]);
    let goal = goal_of(&state);
    let config = SimpConfig::new();
    let lemmas = collect_simp_lemmas(&state, &config);

    let target = app1("f", const_("x"));
    let result = simp_expr(&state, &goal, &target, &lemmas, &config);

    assert_eq!(
        result.expr,
        const_("x"),
        "a reflexive side condition is dischargeable by `Eq.refl`"
    );
    let proof = result
        .proof
        .as_ref()
        .expect("an rfl-discharged rewrite must carry a proof term");
    assert_proves_rewrite(&state, &goal, proof, &target, &const_("x"));
}

// ============================================================================
// Positive: a premise only the RECURSIVE simp stage can close
// ============================================================================

/// `f_id_of_g : ∀ (a : N), (g a = a) → f a = a` over an opaque `g`, with the
/// UNCONDITIONAL `g_id : ∀ (a : N), g a = a` also in the simp set.
///
/// The side condition `g x = x` is reachable by no other stage: there is no
/// hypothesis (so not `assumption`), and `g` is an axiom with no body (so `g x`
/// is not def-eq to `x` and `Eq.refl` does not apply). Only "simp the premise,
/// then discharge the normalized `x = x`" closes it.
fn env_needing_recursive_discharge() -> Environment {
    let mut env = setup_env_with_full_eq();
    add_unary_fn(&mut env, "f");
    add_unary_fn(&mut env, "g");
    add_unconditional_simp_lemma(&mut env, "g_id", "g");
    let premise = make_eq_n(app1("g", Expr::bvar(0)), Expr::bvar(0));
    add_conditional_simp_lemma(&mut env, "f_id_of_g", "f", premise);
    env
}

#[test]
fn test_simp_conditional_lemma_premise_closed_by_recursive_simp() {
    let state = state_with_hyps(env_needing_recursive_discharge(), &[]);
    let goal = goal_of(&state);
    let config = SimpConfig::new();
    let lemmas = collect_simp_lemmas(&state, &config);

    let target = app1("f", const_("x"));
    let result = simp_expr(&state, &goal, &target, &lemmas, &config);

    assert_eq!(
        result.expr,
        const_("x"),
        "the premise `g x = x` normalizes to `x = x`, which is dischargeable"
    );
    let proof = result
        .proof
        .as_ref()
        .expect("a recursively-discharged rewrite must carry a proof term");
    assert_proves_rewrite(&state, &goal, proof, &target, &const_("x"));
}

// The same environment with the recursion budget spent: the premise is now
// unreachable, so the rewrite must be abandoned. This is what bounds the
// discharger.
#[test]
fn test_simp_recursive_discharge_respects_the_depth_budget() {
    let state = state_with_hyps(env_needing_recursive_discharge(), &[]);
    let goal = goal_of(&state);
    let config = SimpConfig {
        discharge_depth: 0,
        ..SimpConfig::new()
    };
    let lemmas = collect_simp_lemmas(&state, &config);

    let target = app1("f", const_("x"));
    let result = simp_expr(&state, &goal, &target, &lemmas, &config);

    assert_eq!(
        result.expr, target,
        "with no recursion budget the premise is undischargeable and the \
         rewrite must be abandoned"
    );
    assert!(result.proof.is_none());
}

// ============================================================================
// Local hypotheses shadow environment constants
// ============================================================================

// `simp only [h]` where `h` is a LOCAL hypothesis that happens to share its
// name with an environment constant. The premise search must read the LOCAL
// rule (which has none), not the constant's telescope — otherwise a side
// condition belonging to a completely different lemma is demanded and the
// perfectly good local rewrite is abandoned.
#[test]
fn test_simp_local_lemma_shadowing_env_constant_is_not_given_its_premises() {
    let mut env = setup_env_with_full_eq();
    add_unary_fn(&mut env, "f");
    let f_x = app1("f", const_("x"));

    // An environment constant named `h`, CONDITIONAL on `P x`.
    add_axiom(
        &mut env,
        "h",
        Expr::pi(
            BinderInfo::Default,
            p_of(const_("x")),
            make_eq_n(f_x.clone(), const_("x")),
        ),
    );

    // A local hypothesis, also named `h`, that is UNCONDITIONAL.
    let state = state_with_hyps(env, &[("h", make_eq_n(f_x.clone(), const_("x")))]);
    let goal = goal_of(&state);
    let config = SimpConfig {
        only: true,
        extra_lemmas: vec!["h".to_string()],
        ..SimpConfig::new()
    };
    let lemmas = collect_simp_lemmas(&state, &config);

    let result = simp_expr(&state, &goal, &f_x, &lemmas, &config);

    assert_eq!(
        result.expr,
        const_("x"),
        "the LOCAL `h` is unconditional and must still rewrite"
    );
    let proof = result
        .proof
        .as_ref()
        .expect("a local-hypothesis rewrite must carry a proof term");
    assert_proves_rewrite(&state, &goal, proof, &f_x, &const_("x"));
}

// `discharge_depth: 0` still allows the non-recursive stages: the budget bounds
// RECURSION, it does not switch the feature off.
#[test]
fn test_simp_conditional_lemma_zero_depth_keeps_non_recursive_stages() {
    let mut env = setup_env_with_full_eq();
    add_unary_fn(&mut env, "f");
    add_conditional_simp_lemma(&mut env, "f_id_of_p", "f", p_of(Expr::bvar(0)));

    let state = state_with_hyps(env, &[("h", p_of(const_("x")))]);
    let goal = goal_of(&state);
    let config = SimpConfig {
        discharge_depth: 0,
        ..SimpConfig::new()
    };
    let lemmas = collect_simp_lemmas(&state, &config);

    let target = app1("f", const_("x"));
    let result = simp_expr(&state, &goal, &target, &lemmas, &config);

    assert_eq!(
        result.expr,
        const_("x"),
        "`assumption` discharge does not consume recursion budget"
    );
    let proof = result
        .proof
        .as_ref()
        .expect("a conditional rewrite must carry a proof term");
    assert_proves_rewrite(&state, &goal, proof, &target, &const_("x"));
}

// ============================================================================
// Loop guard
// ============================================================================

// A conditional lemma whose premise IS its own conclusion: discharging
// `f x = x` requires rewriting `f x`, which requires discharging `f x = x`, …
// The `discharge_depth` budget must cut this off. The test completing (rather
// than hanging or overflowing the stack) is the termination assertion.
#[test]
fn test_simp_self_referential_premise_terminates_without_rewriting() {
    let mut env = setup_env_with_full_eq();
    add_unary_fn(&mut env, "f");
    let self_premise = make_eq_n(app1("f", Expr::bvar(0)), Expr::bvar(0));
    add_conditional_simp_lemma(&mut env, "f_id_of_self", "f", self_premise);

    let state = state_with_hyps(env, &[]);
    let goal = goal_of(&state);
    let config = SimpConfig::new();
    let lemmas = collect_simp_lemmas(&state, &config);

    let target = app1("f", const_("x"));
    let result = simp_expr(&state, &goal, &target, &lemmas, &config);

    assert_eq!(
        result.expr, target,
        "a self-referential side condition must run out of budget, not loop"
    );
    assert!(result.proof.is_none());
}

// The same lemma WITH the premise in context fires immediately via
// `assumption`, showing the loop guard did not simply disable the lemma.
#[test]
fn test_simp_self_referential_premise_still_fires_from_assumption() {
    let mut env = setup_env_with_full_eq();
    add_unary_fn(&mut env, "f");
    let self_premise = make_eq_n(app1("f", Expr::bvar(0)), Expr::bvar(0));
    add_conditional_simp_lemma(&mut env, "f_id_of_self", "f", self_premise);

    let target = app1("f", const_("x"));
    let state = state_with_hyps(env, &[("h", make_eq_n(target.clone(), const_("x")))]);
    let goal = goal_of(&state);
    let config = SimpConfig::new();
    let lemmas = collect_simp_lemmas(&state, &config);

    let result = simp_expr(&state, &goal, &target, &lemmas, &config);

    assert_eq!(result.expr, const_("x"));
    let proof = result
        .proof
        .as_ref()
        .expect("assumption-discharged rewrite must carry a proof term");
    assert_proves_rewrite(&state, &goal, proof, &target, &const_("x"));
}

// ============================================================================
// Binder-type extraction (the de Bruijn arithmetic the discharger depends on)
// ============================================================================

// `∀ (a b : N), P b → <eq>` — three binders, and the premise's own indices must
// be lifted into the CONCLUSION's context: `b` reads as BVar 1 there, not
// BVar 0.
#[test]
fn test_collect_binder_types_lifts_premise_into_conclusion_context() {
    let ty = Expr::pi(
        BinderInfo::Default,
        n_ty(),
        Expr::pi(
            BinderInfo::Default,
            n_ty(),
            Expr::pi(
                BinderInfo::Default,
                // At this binder, `b` is BVar 0 and `a` is BVar 1.
                p_of(Expr::bvar(0)),
                make_eq_n(Expr::bvar(2), Expr::bvar(1)),
            ),
        ),
    );

    let binders = super::expr::collect_binder_types_in_conclusion(&ty);

    assert_eq!(binders.len(), 3, "three leading Pi binders");
    // Index 0 is the INNERMOST binder — the premise.
    assert_eq!(
        binders[0],
        p_of(Expr::bvar(1)),
        "the premise `P b` must be lifted so `b` reads as BVar 1 in the conclusion"
    );
    assert_eq!(binders[1], n_ty(), "binder `b` has type N");
    assert_eq!(binders[2], n_ty(), "binder `a` has type N");
}

// No binders at all: an unconditional, fully-applied lemma statement.
#[test]
fn test_collect_binder_types_no_binders_is_empty() {
    let ty = make_eq_n(const_("x"), const_("x"));
    assert!(super::expr::collect_binder_types_in_conclusion(&ty).is_empty());
}
