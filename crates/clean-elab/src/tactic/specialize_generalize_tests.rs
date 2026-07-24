// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for specialize_multi, generalize_at, revert_many, and revert_with_deps.
//!
//! Part of #3082: validates multi-argument specialization, hypothesis-targeted
//! generalization, and dependency-aware revert.

use clean_kernel::env::Declaration;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Environment, Expr, ExprKind, Level};

use super::core::{ProofState, TacticError};
use super::proof_term::intro;
use super::specialize_generalize::{
    generalize_at, generalize_in_goal, revert_many, revert_single, revert_with_deps,
    specialize_multi, specialize_single,
};

// ---------------------------------------------------------------------------
// Environment helpers
// ---------------------------------------------------------------------------

fn setup_nat_env() -> Environment {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env
}

/// Set up an environment with axiom types for well-typed tests.
///
/// Declares:
///   A : Type
///   P : A -> Prop
///   a : A
///   b : A
///   pa : P a
fn setup_type_env() -> Environment {
    let mut env = Environment::new();
    let type_ = Expr::type_();
    let prop = Expr::sort(Level::zero());
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: type_.clone(),
    })
    .expect("add A");
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    // P : A -> Prop
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::arrow(a_ty.clone(), prop.clone()),
    })
    .expect("add P");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("a"),
        level_params: vec![],
        type_: a_ty.clone(),
    })
    .expect("add a");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("b"),
        level_params: vec![],
        type_: a_ty.clone(),
    })
    .expect("add b");
    // pa : P a
    let p_a = Expr::app(
        Expr::const_(Name::from_string("P"), vec![]),
        Expr::const_(Name::from_string("a"), vec![]),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("pa"),
        level_params: vec![],
        type_: p_a,
    })
    .expect("add pa");
    env
}

/// Create a Nat type expression.
fn nat_ty() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

/// Create a Nat literal expression.
fn nat_lit(n: u64) -> Expr {
    Expr::nat_lit(n)
}

/// Create a type A expression (axiom-based).
fn a_ty() -> Expr {
    Expr::const_(Name::from_string("A"), vec![])
}

/// Create P : A -> Prop expression.
fn p_const() -> Expr {
    Expr::const_(Name::from_string("P"), vec![])
}

/// Create a constant `a : A` expression.
fn a_const() -> Expr {
    Expr::const_(Name::from_string("a"), vec![])
}

/// Create a constant `b : A` expression.
fn b_const() -> Expr {
    Expr::const_(Name::from_string("b"), vec![])
}

// ---------------------------------------------------------------------------
// specialize_single tests
// ---------------------------------------------------------------------------

#[test]
fn test_specialize_single_arg() {
    let env = setup_nat_env();
    // Goal: forall (x : Nat), Nat
    let target = Expr::pi(BinderInfo::Default, nat_ty(), nat_ty());
    let mut state = ProofState::new(env, target);

    // Introduce h : forall (y : Nat), Nat
    intro(&mut state, "h").unwrap();

    // Now we have h : Nat in context, goal is Nat.
    // We need a hypothesis that's actually a Pi type.
    // Let's set up a better test: goal is (forall x, Nat) -> Nat
    let env2 = setup_nat_env();
    let inner_pi = Expr::pi(BinderInfo::Default, nat_ty(), nat_ty());
    let target2 = Expr::arrow(inner_pi, nat_ty());
    let mut state2 = ProofState::new(env2, target2);

    intro(&mut state2, "h").unwrap();

    // h : forall (x : Nat), Nat. Specialize with 0.
    let result = specialize_single(&mut state2, "h", nat_lit(0));
    assert!(result.is_ok(), "specialize with Nat literal should succeed");

    // After specialization, h should have type Nat (codomain instantiated)
    let goal = state2.current_goal().unwrap();
    let h_decl = goal.local_ctx.iter().find(|d| d.name == "h");
    assert!(h_decl.is_some(), "h should still exist after specialize");
}

#[test]
fn test_specialize_nonexistent_fails() {
    let env = setup_nat_env();
    let mut state = ProofState::new(env, nat_ty());

    let result = specialize_single(&mut state, "ghost", nat_lit(0));
    assert!(
        matches!(result, Err(TacticError::HypothesisNotFound(_))),
        "specialize on nonexistent hypothesis should fail"
    );
}

// ---------------------------------------------------------------------------
// specialize_multi tests
// ---------------------------------------------------------------------------

#[test]
fn test_specialize_multiple_args() {
    let env = setup_nat_env();
    // Build: forall (x : Nat) (y : Nat), Nat -> Nat
    // i.e., (forall x y, Nat) -> Nat
    let inner = Expr::pi(
        BinderInfo::Default,
        nat_ty(),
        Expr::pi(BinderInfo::Default, nat_ty(), nat_ty()),
    );
    let target = Expr::arrow(inner, nat_ty());
    let mut state = ProofState::new(env, target);

    intro(&mut state, "h").unwrap();

    // h : forall (x : Nat) (y : Nat), Nat
    // Specialize with two args
    let result = specialize_multi(&mut state, "h", &[nat_lit(1), nat_lit(2)]);
    assert!(
        result.is_ok(),
        "specialize_multi with two Nat args should succeed"
    );

    // After both specializations, h should be Nat
    let goal = state.current_goal().unwrap();
    let h_decl = goal.local_ctx.iter().find(|d| d.name == "h");
    assert!(h_decl.is_some(), "h should exist after multi-specialize");
}

#[test]
fn test_specialize_multi_empty_args() {
    let env = setup_nat_env();
    let mut state = ProofState::new(env, nat_ty());

    // Empty args should be a no-op
    let result = specialize_multi(&mut state, "anything", &[]);
    assert!(
        result.is_ok(),
        "specialize_multi with no args should be no-op"
    );
}

#[test]
fn test_specialize_multi_nonexistent_fails() {
    let env = setup_nat_env();
    let mut state = ProofState::new(env, nat_ty());

    let result = specialize_multi(&mut state, "ghost", &[nat_lit(0)]);
    assert!(
        matches!(result, Err(TacticError::HypothesisNotFound(_))),
        "specialize_multi on nonexistent hypothesis should fail"
    );
}

// ---------------------------------------------------------------------------
// Regression: `specialize h a …` must succeed once the arguments are applied —
// the fully-applied result type need NOT itself be a ∀/→. The prior bug
// re-inspected `h` after applying every arg and rejected the non-Pi result,
// so `specialize h 0` on `h : ∀ n, f n` errored with the already-specialized
// type `f 0`. These mirror the CLI teeth against real Lean 4:
//   t1: `∀ n, f n` + [0]      → h : f 0    (Lean accepts)
//   t2: `∀ n m, f n m` + [0,1]→ h : f 0 1  (Lean accepts)
//   t3: `p → q` + [hp]        → h : q      (Lean accepts)
//   neg: `∀ n, f n` + [0,1,2] → Err        (Lean rejects: too many args)
// ---------------------------------------------------------------------------

/// Environment with `f : Nat -> Prop` (a genuine predicate whose applied
/// result `f 0 : Prop` is NOT a Pi — the case the post-application re-check
/// used to wrongly reject).
fn setup_pred1_env() -> Environment {
    let mut env = setup_nat_env();
    let prop = Expr::sort(Level::zero());
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("f"),
        level_params: vec![],
        type_: Expr::arrow(nat_ty(), prop),
    })
    .expect("add f : Nat -> Prop");
    env
}

/// Environment with `f : Nat -> Nat -> Prop`.
fn setup_pred2_env() -> Environment {
    let mut env = setup_nat_env();
    let prop = Expr::sort(Level::zero());
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("f"),
        level_params: vec![],
        type_: Expr::arrow(nat_ty(), Expr::arrow(nat_ty(), prop)),
    })
    .expect("add f : Nat -> Nat -> Prop");
    env
}

fn f_const() -> Expr {
    Expr::const_(Name::from_string("f"), vec![])
}

/// Tooth 1: `specialize h 0` on `h : ∀ n, f n ⊢ f 0`. The result `f 0` is not
/// a Pi; specialize must still succeed and re-bind `h : f 0`.
#[test]
fn test_specialize_single_result_not_pi_succeeds() {
    let env = setup_pred1_env();
    // Goal: (∀ n : Nat, f n) -> f 0
    let f0 = Expr::app(f_const(), nat_lit(0));
    let forall_fn = Expr::pi(
        BinderInfo::Default,
        nat_ty(),
        Expr::app(f_const(), Expr::bvar(0)),
    );
    let target = Expr::arrow(forall_fn, f0.clone());
    let mut state = ProofState::new(env, target);

    intro(&mut state, "h").unwrap();

    let result = specialize_multi(&mut state, "h", &[nat_lit(0)]);
    assert!(
        result.is_ok(),
        "specialize with a non-Pi result type (f 0) must succeed: {:?}",
        result.err()
    );

    // h must now hold the fully-applied, non-Pi type `f 0`.
    let goal = state.current_goal().unwrap();
    let h_decl = goal
        .local_ctx
        .iter()
        .rev()
        .find(|d| d.name == "h")
        .expect("h should exist after specialize");
    let h_ty = state.whnf(goal, &h_decl.ty);
    assert!(
        !matches!(h_ty.kind(), ExprKind::Pi(..)),
        "h's specialized type should be the non-Pi `f 0`, got {:?}",
        h_ty
    );
}

/// Tooth 2: `specialize h 0 1` on `h : ∀ n m, f n m ⊢ f 0 1`.
#[test]
fn test_specialize_two_args_result_not_pi_succeeds() {
    let env = setup_pred2_env();
    // ∀ n m : Nat, f n m
    let f_nm = Expr::app(Expr::app(f_const(), Expr::bvar(1)), Expr::bvar(0));
    let forall_nm = Expr::pi(
        BinderInfo::Default,
        nat_ty(),
        Expr::pi(BinderInfo::Default, nat_ty(), f_nm),
    );
    // Goal: (∀ n m, f n m) -> f 0 1
    let f01 = Expr::app(Expr::app(f_const(), nat_lit(0)), nat_lit(1));
    let target = Expr::arrow(forall_nm, f01);
    let mut state = ProofState::new(env, target);

    intro(&mut state, "h").unwrap();

    let result = specialize_multi(&mut state, "h", &[nat_lit(0), nat_lit(1)]);
    assert!(
        result.is_ok(),
        "specialize with two args ending in a non-Pi result (f 0 1) must succeed: {:?}",
        result.err()
    );
}

/// Tooth 3: `specialize h hp` on `h : p → q, hp : p ⊢ q`. The codomain `q` is
/// a bare Prop (not a Pi); specialize must re-bind `h : q`.
#[test]
fn test_specialize_implication_codomain_not_pi_succeeds() {
    let mut env = Environment::new();
    let prop = Expr::sort(Level::zero());
    for name in ["p", "q"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: prop.clone(),
        })
        .expect("add prop axiom");
    }
    let p = Expr::const_(Name::from_string("p"), vec![]);
    let q = Expr::const_(Name::from_string("q"), vec![]);
    // Goal: (p -> q) -> p -> q
    let target = Expr::arrow(
        Expr::arrow(p.clone(), q.clone()),
        Expr::arrow(p.clone(), q.clone()),
    );
    let mut state = ProofState::new(env, target);

    intro(&mut state, "h").unwrap(); // h : p -> q
    intro(&mut state, "hp").unwrap(); // hp : p

    let hp = {
        let goal = state.current_goal().unwrap();
        let decl = goal.local_ctx.iter().find(|d| d.name == "hp").unwrap();
        Expr::fvar(decl.fvar)
    };
    let result = specialize_multi(&mut state, "h", &[hp]);
    assert!(
        result.is_ok(),
        "specialize on an implication (codomain q is a bare Prop) must succeed: {:?}",
        result.err()
    );
}

/// Negative: `specialize h 0 1 2` on `h : ∀ n, f n` (only ONE binder). The
/// first arg applies (→ f 0); the second arg has no Pi to consume, so
/// specialize must FAIL CLOSED — a graceful error, never over-applying and
/// never panicking.
#[test]
fn test_specialize_too_many_args_fails_closed() {
    let env = setup_pred1_env();
    let forall_fn = Expr::pi(
        BinderInfo::Default,
        nat_ty(),
        Expr::app(f_const(), Expr::bvar(0)),
    );
    // Goal: (∀ n, f n) -> f 0
    let target = Expr::arrow(forall_fn, Expr::app(f_const(), nat_lit(0)));
    let mut state = ProofState::new(env, target);

    intro(&mut state, "h").unwrap();

    let result = specialize_multi(&mut state, "h", &[nat_lit(0), nat_lit(1), nat_lit(2)]);
    assert!(
        matches!(result, Err(TacticError::GoalMismatch(_))),
        "specialize with more args than binders must fail closed (GoalMismatch), got {:?}",
        result
    );
}

// ---------------------------------------------------------------------------
// generalize_in_goal tests
// ---------------------------------------------------------------------------

#[test]
fn test_generalize_replaces_term() {
    let env = setup_nat_env();
    // Goal contains a specific Nat literal
    // We use Nat.zero as a simple constant that appears in the goal
    let _zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // Goal: Nat.zero = Nat.zero (represented as equality if Eq available,
    // but we can just test with a simpler type containing the term)
    // For simplicity, use arrow: Nat.zero -> Nat (won't type check but tests structure)
    let target = Expr::arrow(nat_ty(), nat_ty());
    let mut state = ProofState::new(env, target);

    // The term `42` does not occur in the `Nat -> Nat` goal. Matching Lean 4,
    // `generalize` is NOT an error in this case: it introduces the fresh
    // variable `n` and leaves the goal otherwise unchanged (no occurrence to
    // abstract). Verified against `lean`: `generalize n + 1 = m` on a goal not
    // mentioning `n + 1` succeeds.
    generalize_in_goal(&mut state, nat_lit(42), "n")
        .expect("generalize over an absent term should still introduce n (Lean 4 semantics)");

    let goal = state
        .current_goal()
        .expect("a goal should remain after generalize");
    assert!(
        goal.local_ctx.iter().any(|d| d.name == "n"),
        "generalize should introduce the fresh variable n even when the term is absent"
    );
}

// ---------------------------------------------------------------------------
// generalize_at tests
// ---------------------------------------------------------------------------

#[test]
fn test_generalize_at_hypothesis() {
    let env = setup_type_env();

    // Use axiom-based types so infer_type works.
    // Goal: P a -> A (well-typed since P a : Prop, A : Type).
    // After intro "h": h : P a |- A.
    let a = a_const();
    let p_a = Expr::app(p_const(), a.clone());
    let a_type = a_ty();
    let target = Expr::arrow(p_a.clone(), a_type.clone());
    let mut state = ProofState::new(env, target);

    intro(&mut state, "h").unwrap();

    // h has type: P a. Generalizing only that local would change its type to
    // `forall (n : A), P n`, which is not definitionally equal to `P a` and
    // comes with no proof that can transport the surrounding goal.  The local
    // replacement boundary must therefore fail closed rather than retype the
    // existing FVar/metavariable scope in place.
    let old_goal = state.current_goal().unwrap().clone();
    let result = generalize_at(&mut state, a, "n", "h");
    assert!(
        matches!(result, Err(TacticError::GoalMismatch(ref detail)) if detail.contains("explicit proof")),
        "generalize_at without a transport proof must fail closed, got: {result:?}"
    );

    let goal = state.current_goal().unwrap();
    assert_eq!(goal.meta_id, old_goal.meta_id);
    assert_eq!(goal.target, old_goal.target);
    assert_eq!(goal.local_ctx.len(), old_goal.local_ctx.len());
    for (actual, expected) in goal.local_ctx.iter().zip(&old_goal.local_ctx) {
        assert_eq!(actual.fvar, expected.fvar);
        assert_eq!(actual.name, expected.name);
        assert_eq!(actual.ty, expected.ty);
        assert_eq!(actual.value, expected.value);
    }
    assert!(!state.metas().is_assigned(old_goal.meta_id));
}

#[test]
fn test_generalize_at_term_not_in_hyp() {
    let env = setup_nat_env();
    let target = Expr::arrow(nat_ty(), nat_ty());
    let mut state = ProofState::new(env, target);

    intro(&mut state, "h").unwrap();

    // h : Nat, try to generalize nat_lit(99) which doesn't appear in Nat
    let result = generalize_at(&mut state, nat_lit(99), "n", "h");
    assert!(
        matches!(result, Err(TacticError::InvalidTarget { .. })),
        "generalize_at should fail when term not in hypothesis"
    );
}

#[test]
fn test_generalize_at_nonexistent_hyp() {
    let env = setup_nat_env();
    let mut state = ProofState::new(env, nat_ty());

    let result = generalize_at(&mut state, nat_lit(5), "n", "ghost");
    assert!(
        matches!(result, Err(TacticError::HypothesisNotFound(_))),
        "generalize_at should fail for nonexistent hypothesis"
    );
}

// ---------------------------------------------------------------------------
// revert_single tests
// ---------------------------------------------------------------------------

#[test]
fn test_revert_moves_to_goal() {
    let env = setup_nat_env();
    // Goal: Nat -> Nat
    let target = Expr::arrow(nat_ty(), nat_ty());
    let mut state = ProofState::new(env, target);

    intro(&mut state, "x").unwrap();
    // Now: x : Nat |- Nat

    revert_single(&mut state, "x").unwrap();

    // After revert: |- Nat -> Nat (Pi type)
    let goal = state.current_goal().unwrap();
    match goal.target.kind() {
        ExprKind::Pi(..) => {} // Expected
        other => panic!("expected Pi after revert, got {:?}", other),
    }

    // x should no longer be in context
    assert!(
        goal.local_ctx.iter().all(|d| d.name != "x"),
        "x should be removed from context after revert"
    );
}

// ---------------------------------------------------------------------------
// revert_many tests
// ---------------------------------------------------------------------------

#[test]
fn test_revert_multiple() {
    let env = setup_nat_env();
    // Goal: Nat -> Nat -> Nat
    let target = Expr::arrow(nat_ty(), Expr::arrow(nat_ty(), nat_ty()));
    let mut state = ProofState::new(env, target);

    intro(&mut state, "x").unwrap();
    intro(&mut state, "y").unwrap();
    // Now: x : Nat, y : Nat |- Nat

    revert_many(&mut state, &["y", "x"]).unwrap();

    // After revert: |- Nat -> Nat -> Nat
    let goal = state.current_goal().unwrap();
    assert!(
        goal.local_ctx.is_empty(),
        "all hypotheses should be reverted"
    );
    // Target should be a double Pi
    match goal.target.kind() {
        ExprKind::Pi(..) => {} // Expected
        other => panic!("expected Pi after revert_many, got {:?}", other),
    }
}

#[test]
fn test_revert_many_nonexistent_fails() {
    let env = setup_nat_env();
    let target = Expr::arrow(nat_ty(), nat_ty());
    let mut state = ProofState::new(env, target);

    intro(&mut state, "x").unwrap();

    let result = revert_many(&mut state, &["x", "ghost"]);
    // x succeeds, ghost fails
    assert!(
        matches!(result, Err(TacticError::HypothesisNotFound(_))),
        "revert_many should fail on nonexistent hypothesis"
    );
}

// ---------------------------------------------------------------------------
// revert_with_deps tests
// ---------------------------------------------------------------------------

#[test]
fn test_revert_with_dependencies() {
    let env = setup_type_env();

    // Build a goal where h's type depends on x.
    // Target: forall (x : A), P x -> A
    // After intro x: x : A |- P x -> A
    // After intro h: x : A, h : P x |- A
    // h's type mentions fvar(x), so h depends on x.
    let a_type = a_ty();
    let p = p_const();
    let bvar0 = Expr::bvar(0);
    // P (bvar 0) is the body of the inner Pi
    let p_bvar0 = Expr::app(p.clone(), bvar0.clone());
    let inner = Expr::pi(BinderInfo::Default, p_bvar0, a_type.clone());
    let target = Expr::pi(BinderInfo::Default, a_type.clone(), inner);
    let mut state = ProofState::new(env, target);

    intro(&mut state, "x").unwrap();
    intro(&mut state, "h").unwrap();
    // x : A, h : P x |- A

    // Revert x should also revert h (since h's type mentions x's fvar)
    let reverted = revert_with_deps(&mut state, "x").unwrap();

    // Both h and x should be reverted (h first since it depends on x)
    assert!(
        reverted.contains(&"h".to_string()),
        "h should be reverted as dependent of x, reverted: {:?}",
        reverted
    );
    assert!(
        reverted.contains(&"x".to_string()),
        "x should be in the reverted list"
    );

    // Context should be empty
    let goal = state.current_goal().unwrap();
    assert!(
        goal.local_ctx.is_empty(),
        "all hypotheses should be reverted"
    );
}

#[test]
fn test_revert_with_deps_no_dependents() {
    let env = setup_nat_env();
    // Two independent hypotheses
    let target = Expr::arrow(nat_ty(), Expr::arrow(nat_ty(), nat_ty()));
    let mut state = ProofState::new(env, target);

    intro(&mut state, "x").unwrap();
    intro(&mut state, "y").unwrap();
    // x : Nat, y : Nat |- Nat

    // Revert y has no dependents
    let reverted = revert_with_deps(&mut state, "y").unwrap();
    assert_eq!(reverted.len(), 1, "only y should be reverted");
    assert_eq!(reverted[0], "y");

    // x should still be in context
    let goal = state.current_goal().unwrap();
    assert!(
        goal.local_ctx.iter().any(|d| d.name == "x"),
        "x should remain in context"
    );
}

#[test]
fn test_revert_with_deps_nonexistent() {
    let env = setup_nat_env();
    let mut state = ProofState::new(env, nat_ty());

    let result = revert_with_deps(&mut state, "ghost");
    assert!(
        matches!(result, Err(TacticError::HypothesisNotFound(_))),
        "revert_with_deps on nonexistent should fail"
    );
}

// ---------------------------------------------------------------------------
// Roundtrip tests
// ---------------------------------------------------------------------------

#[test]
fn test_revert_then_intro_roundtrip() {
    let env = setup_nat_env();
    let target = Expr::arrow(nat_ty(), nat_ty());
    let mut state = ProofState::new(env, target);

    intro(&mut state, "x").unwrap();
    // x : Nat |- Nat

    revert_single(&mut state, "x").unwrap();
    // |- Nat -> Nat

    intro(&mut state, "x2").unwrap();
    // x2 : Nat |- Nat

    let goal = state.current_goal().unwrap();
    assert_eq!(
        goal.local_ctx.len(),
        1,
        "should have exactly one hypothesis after roundtrip"
    );
    assert_eq!(goal.local_ctx[0].name, "x2");
}
