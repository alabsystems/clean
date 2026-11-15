// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

// =========================================================================
// decide_eq Tests
// =========================================================================

#[test]
fn test_decide_eq_fails_on_non_equality_non_decidable() {
    let env = setup_env();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, a);

    let result = decide_eq(&mut state);
    assert!(matches!(result, Err(TacticError::GoalMismatch(_))));
}

#[test]
fn test_decide_eq_on_equal_nat_literals() {
    // setup_env() lacks Eq/rfl infrastructure, so decide_eq must fail even on 5 = 5
    let env = setup_env();
    let five = Expr::nat_lit(5);
    let eq_goal = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                Expr::const_(Name::from_string("Nat"), vec![]),
            ),
            five.clone(),
        ),
        five.clone(),
    );
    let mut state = ProofState::new(env, eq_goal);

    let result = decide_eq(&mut state);
    // Without Eq.refl in the environment, decide_eq cannot construct a reflexivity proof
    assert!(
        matches!(result, Err(TacticError::EnvironmentMissing { ref constant }) if constant == "rfl" || constant == "Eq.refl"),
        "decide_eq should fail without Eq infrastructure, got: {result:?}"
    );
    assert!(
        !state.is_complete(),
        "goal should remain open after decide_eq failure"
    );
}

#[test]
fn test_decide_eq_on_different_nat_literals() {
    let env = setup_env();
    let five = Expr::nat_lit(5);
    let six = Expr::nat_lit(6);
    let eq_goal = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                Expr::const_(Name::from_string("Nat"), vec![]),
            ),
            five,
        ),
        six,
    );
    let mut state = ProofState::new(env, eq_goal);

    let result = decide_eq(&mut state);
    assert!(
        matches!(result, Err(TacticError::ArithmeticFailed { ref tactic, .. }) if tactic == "decide_eq"),
        "should be ArithmeticFailed from decide_eq, got: {result:?}"
    );
}

#[test]
fn test_match_decidable_eq_pattern() {
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let five = Expr::nat_lit(5);
    let six = Expr::nat_lit(6);

    // Build: Decidable (Eq Nat 5 6)
    let eq_expr = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat_ty.clone(),
            ),
            five.clone(),
        ),
        six.clone(),
    );
    let decidable_expr = Expr::app(
        Expr::const_(Name::from_string("Decidable"), vec![]),
        eq_expr,
    );

    let result = match_decidable_eq(&decidable_expr);
    let result = result.expect("expected Some");
    let (ty, lhs, rhs) = result;
    assert_eq!(ty, nat_ty);
    assert_eq!(lhs, five);
    assert_eq!(rhs, six);
}

#[test]
fn test_decide_eq_is_false_has_implicit_prop_arg() {
    // Regression test for #2461 F3: Decidable.isFalse must include the implicit
    // {p : Prop} argument. Without it, the proof term is ill-typed:
    //   App(Decidable.isFalse, ne_proof)                — 1 arg, WRONG
    //   App(App(Decidable.isFalse, eq_prop), ne_proof)  — 2 args, CORRECT
    //
    // Part of #302: decide_eq now requires the kernel noConfusion path for
    // Nat disequality instead of falling back to trustedAy.
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_true_false().unwrap();
    env.init_nat().unwrap();
    env.init_decidable().unwrap();

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let five = Expr::nat_lit(5);
    let six = Expr::nat_lit(6);
    let eq_expr = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat_ty,
            ),
            five,
        ),
        six,
    );
    let decidable_goal = Expr::app(
        Expr::const_(Name::from_string("Decidable"), vec![]),
        eq_expr,
    );
    let mut state = ProofState::new(env, decidable_goal);

    let result = decide_eq(&mut state);
    assert!(result.is_ok(), "decide_eq should solve Decidable (5 = 6)");
    assert!(state.is_complete(), "goal should be closed");

    let proof = state
        .proof_term()
        .expect("completed state should have proof term");
    let head = proof.get_app_fn();
    let args = proof.get_app_args();

    if let ExprKind::Const(name, _) = head.kind() {
        assert_eq!(
            name.to_string(),
            "Decidable.isFalse",
            "proof head should be Decidable.isFalse, got: {name}",
        );
    } else {
        panic!(
            "proof head should be Const (Decidable.isFalse), got: {:?}",
            head.kind()
        );
    }

    assert_eq!(
        args.len(),
        2,
        "Decidable.isFalse needs 2 args (implicit {{p}} + ne_proof), got {} (#2461 F3)",
        args.len()
    );
}

#[test]
fn test_decidable_type_check() {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let custom = Expr::const_(Name::from_string("CustomType"), vec![]);

    assert!(decidable_type_check(&nat));
    assert!(decidable_type_check(&bool_ty));
    assert!(!decidable_type_check(&custom));
}

#[test]
fn test_eval_to_nat_literals() {
    let five = Expr::nat_lit(5);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    assert_eq!(eval_to_nat(&five), Some(5));
    assert_eq!(eval_to_nat(&zero), Some(0));
}

#[test]
fn test_eval_to_nat_succ() {
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ_zero = Expr::app(Expr::const_(Name::from_string("Nat.succ"), vec![]), zero);

    assert_eq!(eval_to_nat(&succ_zero), Some(1));
}

/// Smoke test for decide_eq with FVar hypotheses in the goal context.
///
/// Verifies that decide_eq doesn't crash or produce wrong errors when the
/// goal target contains FVars from local hypotheses. The is_def_eq check
/// for `n = n` passes via structural identity (def_eq.rs:238: `a == b`)
/// regardless of context, so this test exercises the overall code path
/// (match_equality → is_def_eq → rfl) rather than specifically testing
/// local context availability.
///
/// A stronger test of the #2212 fix would need non-identical expressions
/// that are definitionally equal only with FVar type information (e.g.,
/// eta-expanded FVars or projection reduction over FVar types).
///
/// Re: #2212, #2229
#[test]
fn test_decide_eq_equality_with_fvar_hypothesis() {
    let env = setup_env();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);

    // Create hypothesis n : Nat in goal context
    let n_fvar = FVarId::new(42);
    let local_decl = LocalDecl {
        binder_info: Default::default(),
        fvar: n_fvar,
        name: clean_parser::SurfaceName::generated_path("n"),
        ty: nat_ty.clone(),
        value: None,
    };

    // Goal: ⊢ n = n (where n is a local FVar)
    let n_expr = Expr::fvar(n_fvar);
    let eq_goal = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat_ty,
            ),
            n_expr.clone(),
        ),
        n_expr,
    );
    let mut state = ProofState::with_context(env, eq_goal, vec![local_decl]);

    let result = decide_eq(&mut state);
    // is_def_eq(n, n) passes via structural identity, then rfl() is called.
    // rfl fails because setup_env() lacks Eq.refl infrastructure, but the
    // error should come from the rfl path, not the "cannot evaluate equality"
    // fallthrough (which would indicate is_def_eq returned false).
    if let Err(ref e) = result {
        let msg = e.to_string();
        assert!(
            !msg.contains("cannot evaluate equality"),
            "decide_eq fell through to eval_to_nat instead of taking rfl path: {msg}"
        );
    }
}
