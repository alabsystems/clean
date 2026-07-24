// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Behavioral tests for `simp [foo]` delta-unfolding of `Declaration::Definition`s.
//!
//! #3518 regression coverage: `simp` must unfold `StateT.bind` / `Except.bind`
//! (and any other non-equality definition) when they are supplied as extra
//! lemmas, matching Lean 4 `simp` delta-unfolding semantics. Before the fix,
//! `collect_extra_lemmas` silently dropped definitions whose type is not an
//! equality, so `simp [StateT.bind]` was effectively a no-op.

use super::*;
use clean_kernel::env::Declaration;

/// Build an environment with a base type `N`, a constant `a : N`, an identity
/// function `my_id : N → N := λ x => x`, and an "apply" definition
/// `apply_once : N → N := λ x => my_id x`. Neither definition's type is an
/// equality, so pre-#3518 `simp [my_id]` / `simp [apply_once]` would drop the
/// names and fail to make progress.
fn setup_env_with_defs() -> Environment {
    let mut env = Environment::new();
    env.init_eq().unwrap();

    let n_ty = Expr::type_();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("N"),
        level_params: vec![],
        type_: n_ty,
    })
    .unwrap();

    let n = Expr::const_(Name::from_string("N"), vec![]);

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("a"),
        level_params: vec![],
        type_: n.clone(),
    })
    .unwrap();

    // my_id : N → N := λ x : N => x
    env.add_decl(Declaration::Definition {
        name: Name::from_string("my_id"),
        level_params: vec![],
        type_: Expr::arrow(n.clone(), n.clone()),
        value: Expr::lam(BinderInfo::Default, n.clone(), Expr::bvar(0)),
        is_reducible: false,
    })
    .unwrap();

    // apply_once : N → N := λ x : N => my_id x
    env.add_decl(Declaration::Definition {
        name: Name::from_string("apply_once"),
        level_params: vec![],
        type_: Expr::arrow(n.clone(), n.clone()),
        value: Expr::lam(
            BinderInfo::Default,
            n,
            Expr::app(
                Expr::const_(Name::from_string("my_id"), vec![]),
                Expr::bvar(0),
            ),
        ),
        is_reducible: false,
    })
    .unwrap();

    env
}

/// Build `@Eq.{1} N lhs rhs`.
fn make_eq_n(lhs: Expr, rhs: Expr) -> Expr {
    let n = Expr::const_(Name::from_string("N"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                n,
            ),
            lhs,
        ),
        rhs,
    )
}

/// Direct regression for #3518: `simp [my_id]` must unfold `my_id` in the goal
/// and close `my_id a = a` via the resulting beta-reduction + rfl.
///
/// Before the fix, `my_id` is a non-equality `Declaration::Definition`, so
/// `collect_extra_lemmas` silently dropped it. `simp` then found no applicable
/// rewrite and reported `NoProgress`.
#[test]
fn test_simp_unfolds_user_supplied_definition_close_via_rfl() {
    let env = setup_env_with_defs();

    let my_id = Expr::const_(Name::from_string("my_id"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    // Goal: my_id a = a
    let goal = make_eq_n(Expr::app(my_id, a.clone()), a);
    let mut state = ProofState::new(env, goal);

    let mut config = SimpConfig::new();
    config.extra_lemmas.push("my_id".to_string());

    simp(&mut state, config).expect("simp [my_id] should unfold my_id and close via rfl");
    assert!(
        state.goals().is_empty(),
        "simp [my_id] should close `my_id a = a` but {} goals remain",
        state.goals().len()
    );
}

/// Nested unfolding: `simp [my_id, apply_once]` must unfold both through two
/// layers of definition indirection, then beta-reduce, then close via rfl on
/// `apply_once a = a`. Models the monadic `StateT.bind` / `Except.bind` case
/// from #3518 where nested definitions need to unfold together.
#[test]
fn test_simp_unfolds_multiple_definitions_nested() {
    let env = setup_env_with_defs();

    let apply_once = Expr::const_(Name::from_string("apply_once"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    // Goal: apply_once a = a
    let goal = make_eq_n(Expr::app(apply_once, a.clone()), a);
    let mut state = ProofState::new(env, goal);

    let mut config = SimpConfig::new();
    config.extra_lemmas.push("apply_once".to_string());
    config.extra_lemmas.push("my_id".to_string());

    simp(&mut state, config)
        .expect("simp [apply_once, my_id] should unfold both and close via rfl");
    assert!(
        state.goals().is_empty(),
        "nested unfold should close `apply_once a = a` but {} goals remain",
        state.goals().len()
    );
}

/// `simp only [my_id]` (without built-in/@[simp] lemmas) should still unfold
/// the definition. This is important because monadic proofs in the wild use
/// `simp only [StateT.bind, ...]` to restrict the rewrite set.
#[test]
fn test_simp_only_unfolds_user_supplied_definition() {
    let env = setup_env_with_defs();

    let my_id = Expr::const_(Name::from_string("my_id"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    let goal = make_eq_n(Expr::app(my_id, a.clone()), a);
    let mut state = ProofState::new(env, goal);

    simp_only(&mut state, vec!["my_id".to_string()])
        .expect("simp only [my_id] should unfold my_id and close via rfl");
    assert!(state.goals().is_empty());
}

/// `simp only [foo] at h` (hypothesis variant) must unfold the definition in
/// the hypothesis type, matching the goal-side behaviour from #3518. This is a
/// regression test for #3529: before the fix, `simp_only_at` did not seed
/// `config.unfold_defs` from `extra_lemmas`, so `simp only [double] at h`
/// returned `NoProgress` even when `double` was a bare definition that should
/// beta-unfold in the hypothesis.
#[test]
fn test_simp_only_at_unfolds_user_supplied_definition_in_hypothesis() {
    let env = setup_env_with_defs();

    let my_id = Expr::const_(Name::from_string("my_id"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    // h : my_id a = a
    let h_ty = make_eq_n(Expr::app(my_id, a.clone()), a.clone());
    // Goal: (arbitrary Prop-ish) — we only care about what happens to `h`.
    let target = Expr::const_(Name::from_string("N"), vec![]);
    let mut state = ProofState::with_context(
        env,
        target,
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: h_ty.clone(),
            value: None,
        }],
    );

    let result = simp_only_at(&mut state, "h", vec!["my_id".to_string()]);
    assert!(
        result.is_ok(),
        "simp only [my_id] at h should unfold my_id in the hypothesis: {result:?}"
    );

    let goal = state.current_goal().expect("goal should still exist");
    let h = goal
        .local_ctx
        .iter()
        .find(|d| d.name == "h")
        .expect("h should still be in context");
    assert_ne!(
        h.ty, h_ty,
        "hypothesis h should have been rewritten by unfold + beta reduction"
    );
}

/// Nested `simp only [apply_once, my_id] at h` must unfold both definitions in
/// the hypothesis, mirroring the goal-side nested-unfold test from #3518.
/// Models the monadic `StateT.bind` + `Except.bind` + `pure` stack in #3529
/// where `simp only [...]` must unfold every name simultaneously inside a
/// hypothesis.
#[test]
fn test_simp_only_at_unfolds_multiple_definitions_in_hypothesis() {
    let env = setup_env_with_defs();

    let apply_once = Expr::const_(Name::from_string("apply_once"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    // h : apply_once a = a
    let h_ty = make_eq_n(Expr::app(apply_once, a.clone()), a.clone());
    let target = Expr::const_(Name::from_string("N"), vec![]);
    let mut state = ProofState::with_context(
        env,
        target,
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: h_ty.clone(),
            value: None,
        }],
    );

    let result = simp_only_at(
        &mut state,
        "h",
        vec!["apply_once".to_string(), "my_id".to_string()],
    );
    assert!(
        result.is_ok(),
        "simp only [apply_once, my_id] at h should unfold both: {result:?}"
    );

    let goal = state.current_goal().expect("goal should still exist");
    let h = goal
        .local_ctx
        .iter()
        .find(|d| d.name == "h")
        .expect("h should still be in context");
    assert_ne!(
        h.ty, h_ty,
        "nested unfold should simplify hypothesis past its original form"
    );
}

/// Axioms do NOT have a body and MUST NOT be registered as unfold targets.
/// `simp [some_axiom]` must behave as it did pre-#3518: the lemma is simply
/// ignored if its type isn't an equality, not treated as an unfoldable
/// definition (which would panic or misbehave since there's no body).
#[test]
fn test_simp_does_not_unfold_axioms() {
    let mut env = setup_env_with_defs();

    // Add an axiom `b : N` — no body, so it cannot be delta-unfolded.
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("b"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("N"), vec![]),
    })
    .unwrap();

    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    // Goal: b = a (not provable; b is distinct from a). We are only checking
    // that `simp [b]` does not crash / does not claim to unfold `b`.
    let goal = make_eq_n(b, a);
    let mut state = ProofState::new(env, goal);

    let mut config = SimpConfig::new();
    config.only_simplify = true; // don't try to close — just verify no crash
    config.extra_lemmas.push("b".to_string());

    let result = simp(&mut state, config);
    // We expect NoProgress: `b` is an axiom and cannot be unfolded, so
    // simp finds nothing to do. The critical invariant is that it does NOT
    // silently replace `b` with a bogus value.
    assert!(
        matches!(result, Err(TacticError::NoProgress { .. })),
        "simp [axiom] should report NoProgress, got: {result:?}"
    );
}
