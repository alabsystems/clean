// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for rewrite chain, RewriteDirection/RewriteRule types, and subst tactics.
//!
//! Complements equality.rs which covers basic rewrite/symm/trans/calc_trans.
//! Part of #3082: rewrite and substitution tactic implementation.

use super::*;
use crate::unify::MetaId;

// ==========================================================================
// RewriteDirection enum tests
// ==========================================================================

#[test]
fn test_rewrite_direction_forward_is_not_reverse() {
    let dir = RewriteDirection::Forward;
    assert!(!dir.is_reverse(), "Forward should not be reverse");
}

#[test]
fn test_rewrite_direction_backward_is_reverse() {
    let dir = RewriteDirection::Backward;
    assert!(dir.is_reverse(), "Backward should be reverse");
}

#[test]
fn test_rewrite_direction_equality() {
    assert_eq!(RewriteDirection::Forward, RewriteDirection::Forward);
    assert_eq!(RewriteDirection::Backward, RewriteDirection::Backward);
    assert_ne!(RewriteDirection::Forward, RewriteDirection::Backward);
}

#[test]
fn test_rewrite_direction_clone_copy() {
    let dir = RewriteDirection::Forward;
    let cloned = dir;
    assert_eq!(dir, cloned, "RewriteDirection should be Copy");
}

// ==========================================================================
// RewriteRule struct tests
// ==========================================================================

#[test]
fn test_rewrite_rule_from_hypothesis_forward() {
    let env = setup_env_with_full_eq();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);

    let target = make_p(x.clone());
    let h_ty = make_eq_n(x.clone(), y.clone());

    let state = ProofState::with_context(
        env,
        target,
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: h_ty,
            value: None,
        }],
    );

    let goal = state.current_goal().unwrap().clone();
    let rule = RewriteRule::from_hypothesis(&state, &goal, "h", RewriteDirection::Forward)
        .expect("should build rule from hypothesis");

    assert_eq!(rule.direction, RewriteDirection::Forward);
    assert_eq!(*rule.from_expr(), x, "forward from should be LHS");
    assert_eq!(*rule.to_expr(), y, "forward to should be RHS");
    assert_eq!(rule.lhs, x);
    assert_eq!(rule.rhs, y);
}

#[test]
fn test_rewrite_rule_from_hypothesis_backward() {
    let env = setup_env_with_full_eq();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);

    let target = make_p(y.clone());
    let h_ty = make_eq_n(x.clone(), y.clone());

    let state = ProofState::with_context(
        env,
        target,
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: h_ty,
            value: None,
        }],
    );

    let goal = state.current_goal().unwrap().clone();
    let rule = RewriteRule::from_hypothesis(&state, &goal, "h", RewriteDirection::Backward)
        .expect("should build rule from hypothesis");

    assert_eq!(rule.direction, RewriteDirection::Backward);
    assert_eq!(*rule.from_expr(), y, "backward from should be RHS");
    assert_eq!(*rule.to_expr(), x, "backward to should be LHS");
}

#[test]
fn test_rewrite_rule_missing_hypothesis() {
    let env = setup_env_with_full_eq();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let target = make_p(x);

    let state = ProofState::new(env, target);
    let goal = state.current_goal().unwrap().clone();

    let result = RewriteRule::from_hypothesis(&state, &goal, "missing", RewriteDirection::Forward);
    assert!(
        matches!(result, Err(TacticError::HypothesisNotFound(name)) if name == "missing"),
        "should fail for missing hypothesis"
    );
}

#[test]
fn test_rewrite_rule_non_equality_hypothesis() {
    let env = setup_env_with_full_eq();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let target = make_p(x.clone());
    let h_ty = make_p(x); // P(x), not an equality

    let state = ProofState::with_context(
        env,
        target,
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: h_ty,
            value: None,
        }],
    );

    let goal = state.current_goal().unwrap().clone();
    let result = RewriteRule::from_hypothesis(&state, &goal, "h", RewriteDirection::Forward);
    assert!(result.is_err(), "should fail for non-equality hypothesis");
}

// ==========================================================================
// rw fallback to environment constants (rw [Nat.add_comm], imported lemmas)
// ==========================================================================

/// `setup_env_with_full_eq` (type N, x/y/z : N, P : N → Prop) plus a unary
/// `g : N → N` so quantified rewrite rules have a non-trivial LHS.
fn setup_env_with_g() -> Environment {
    let mut env = setup_env_with_full_eq();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("g"),
        level_params: vec![],
        type_: Expr::arrow(
            Expr::const_(Name::from_string("N"), vec![]),
            Expr::const_(Name::from_string("N"), vec![]),
        ),
    })
    .unwrap();
    env
}

/// Confirm `close_goal` accepted a kernel-valid proof for the closed goal: the
/// term assigned to the original root metavariable infers a type def-eq to the
/// original target. This pins that the env-sourced rewrite proof type-checks.
fn assert_root_proof_checks(state: &ProofState, root: MetaId, original_target: &Expr) {
    let proof = state
        .metas()
        .get_assignment(root)
        .expect("root goal should be closed with a proof term")
        .clone();
    let proof = state.metas().instantiate(&proof);
    let probe_goal = state.current_goal().cloned().unwrap_or_else(|| Goal {
        meta_id: root,
        target: original_target.clone(),
        local_ctx: Vec::new(),
        tag: None,
    });
    let inferred = state
        .infer_type(&probe_goal, &proof)
        .expect("rewrite proof term must type-check in the kernel");
    assert!(
        state.is_def_eq(&probe_goal, &inferred, original_target),
        "rewrite proof has type {inferred:?}, expected {original_target:?}"
    );
}

/// Independently kernel-re-check the `Eq.subst` cast a `rw [_] at h` installs:
/// `@Eq.subst.{1} N (fun t => P t) from to eq_proof h_old` must infer to the
/// rewritten hypothesis type in the ORIGINAL context that binds `h_old`. This
/// mirrors the fail-closed check inside `replace_local_decl_core` (which infers
/// the cast and requires it def-eq the new hyp type), but builds the cast in the
/// test so the kernel — not the tactic — is the one confirming soundness.
fn assert_eq_subst_cast_checks(
    state: &ProofState,
    orig_goal: &Goal,
    from: Expr,
    to: Expr,
    eq_proof: Expr,
    h_old: FVarId,
    expected_hyp_ty: &Expr,
) {
    let n = Expr::const_(Name::from_string("N"), vec![]);
    let motive = Expr::lam(BinderInfo::Default, n.clone(), make_p(Expr::bvar(0)));
    let eq_subst = Expr::const_(
        Name::from_string("Eq.subst"),
        vec![Level::succ(Level::zero())],
    );
    let cast = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(Expr::app(eq_subst, n), motive), from),
                to,
            ),
            eq_proof,
        ),
        Expr::fvar(h_old),
    );
    let inferred = state
        .infer_type(orig_goal, &cast)
        .expect("the Eq.subst cast the rewrite installs must kernel-check in context");
    assert!(
        state.is_def_eq(orig_goal, &inferred, expected_hyp_ty),
        "Eq.subst cast has type {inferred:?}, expected rewritten hyp {expected_hyp_ty:?}"
    );
}

#[test]
fn test_rewrite_env_const_forward_rewrites_goal() {
    // Env theorem `xy : x = y` with NO matching local hypothesis. `rw [xy]`
    // must fall back to the environment (the gap this unit closes).
    let mut env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("xy"),
        level_params: vec![],
        type_: make_eq_n(x.clone(), y.clone()),
    })
    .unwrap();

    let target = make_p(x.clone());
    let mut state = ProofState::new(env, target.clone());
    let root = state.current_goal().unwrap().meta_id;

    rewrite_ltr(&mut state, "xy").expect("rw [xy] should use the env theorem");

    assert_eq!(
        state.current_goal().unwrap().target,
        make_p(y),
        "goal should become P(y)"
    );
    assert_root_proof_checks(&state, root, &target);
}

#[test]
fn test_rewrite_env_const_backward_rewrites_goal() {
    // `rw [← xy]` with `xy : x = y` rewrites y → x.
    let mut env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("xy"),
        level_params: vec![],
        type_: make_eq_n(x.clone(), y.clone()),
    })
    .unwrap();

    let target = make_p(y.clone());
    let mut state = ProofState::new(env, target.clone());
    let root = state.current_goal().unwrap().meta_id;

    rewrite_rtl(&mut state, "xy").expect("rw [← xy] should use the env theorem");

    assert_eq!(
        state.current_goal().unwrap().target,
        make_p(x),
        "goal should become P(x)"
    );
    assert_root_proof_checks(&state, root, &target);
}

#[test]
fn test_rewrite_env_const_quantified_equation_instantiates() {
    // `gx : ∀ (a : N), g a = a`. `rw [gx]` on goal `P (g x)` must instantiate
    // the leading binder (a := x) by unifying the LHS pattern `g ?a` with `g x`.
    let env = setup_env_with_g();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let g = Expr::const_(Name::from_string("g"), vec![]);
    let g_a = Expr::app(g.clone(), Expr::bvar(0));
    // ∀ (a : N), @Eq.{1} N (g a) a
    let gx_ty = Expr::pi(
        BinderInfo::Default,
        Expr::const_(Name::from_string("N"), vec![]),
        make_eq_n(g_a, Expr::bvar(0)),
    );
    let mut env = env;
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("gx"),
        level_params: vec![],
        type_: gx_ty,
    })
    .unwrap();

    let target = make_p(Expr::app(g, x.clone()));
    let mut state = ProofState::new(env, target.clone());
    let root = state.current_goal().unwrap().meta_id;

    rewrite_ltr(&mut state, "gx").expect("rw [gx] should instantiate ∀ binder and rewrite");

    assert_eq!(
        state.current_goal().unwrap().target,
        make_p(x),
        "goal should become P(x) after instantiating a := x"
    );
    assert_root_proof_checks(&state, root, &target);
}

#[test]
fn test_rewrite_local_hyp_quantified_equation_instantiates() {
    // `h : ∀ (a : N), g a = a` as a LOCAL hypothesis. `rw [h]` on goal `P (g x)`
    // must peel the leading ∀ binder (a := x) — mirroring the env-constant path —
    // and rewrite `g x → x`. Before the binder-peel fix, the local-hyp branch fed
    // the Pi-headed type straight to `match_equality`, which saw a `Pi` head (not
    // `Eq`) and failed. Regression guard for the ∀-quantified-local-hyp rw fix.
    let env = setup_env_with_g();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let g = Expr::const_(Name::from_string("g"), vec![]);
    let g_a = Expr::app(g.clone(), Expr::bvar(0));
    // ∀ (a : N), @Eq.{1} N (g a) a
    let h_ty = Expr::pi(
        BinderInfo::Default,
        Expr::const_(Name::from_string("N"), vec![]),
        make_eq_n(g_a, Expr::bvar(0)),
    );

    let target = make_p(Expr::app(g, x.clone()));
    let mut state = ProofState::with_context(
        env,
        target.clone(),
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: h_ty,
            value: None,
        }],
    );
    let root = state.current_goal().unwrap().meta_id;

    rewrite_ltr(&mut state, "h")
        .expect("rw [h] should peel the ∀ binder of a local hyp and rewrite");

    assert_eq!(
        state.current_goal().unwrap().target,
        make_p(x),
        "goal should become P(x) after instantiating a := x from the local hyp"
    );
    assert_root_proof_checks(&state, root, &target);
}

#[test]
fn test_rewrite_env_const_universe_polymorphic_instantiates() {
    // Genuinely universe-polymorphic lemma. `dup.{u} : ∀ (α : Type u), α → α`
    // and `dup_eq.{u} : ∀ (α : Type u) (a : α), dup α a = a`. Rewriting
    // `P (dup N x)` exercises level-param substitution + universe unification.
    let mut env = setup_env_with_full_eq();
    let u = Name::from_string("u");
    let sort_u = Expr::sort(Level::param(u.clone()));

    // dup.{u} : (α : Type u) → α → α
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("dup"),
        level_params: vec![u.clone()],
        type_: Expr::pi(
            BinderInfo::Default,
            sort_u.clone(),
            Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
        ),
    })
    .unwrap();

    // dup_eq.{u} : (α : Type u) → (a : α) → @Eq.{u} α (dup.{u} α a) a
    let alpha = Expr::bvar(1); // α under the two binders
    let a_var = Expr::bvar(0); // a
    let dup_app = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("dup"), vec![Level::param(u.clone())]),
            alpha.clone(),
        ),
        a_var.clone(),
    );
    let eq_body = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::param(u.clone())]),
                alpha,
            ),
            dup_app,
        ),
        a_var,
    );
    let dup_eq_ty = Expr::pi(
        BinderInfo::Default,
        sort_u,
        Expr::pi(BinderInfo::Default, Expr::bvar(0), eq_body),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("dup_eq"),
        level_params: vec![u],
        type_: dup_eq_ty,
    })
    .unwrap();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let n = Expr::const_(Name::from_string("N"), vec![]);
    let dup_n_x = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("dup"), vec![Level::succ(Level::zero())]),
            n,
        ),
        x.clone(),
    );
    let target = make_p(dup_n_x);
    let mut state = ProofState::new(env, target.clone());
    let root = state.current_goal().unwrap().meta_id;

    rewrite_ltr(&mut state, "dup_eq")
        .expect("rw [dup_eq] should solve universe + value metavars from the goal");

    assert_eq!(
        state.current_goal().unwrap().target,
        make_p(x),
        "goal should become P(x)"
    );
    assert_root_proof_checks(&state, root, &target);
}

#[test]
fn test_rewrite_unknown_name_errors_cleanly() {
    // Neither a local hypothesis nor an env constant: clean HypothesisNotFound.
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let mut state = ProofState::new(env, make_p(x));

    let result = rewrite_ltr(&mut state, "Does.Not.Exist");
    assert!(
        matches!(result, Err(TacticError::HypothesisNotFound(ref name)) if name == "Does.Not.Exist"),
        "unknown rewrite target should be HypothesisNotFound, got {result:?}"
    );
}

#[test]
fn test_rewrite_local_hyp_shadows_env_const_of_same_name() {
    // A local hyp and an env const share the name `xy`. The local hypothesis
    // (`x = z`) must win over the env const (`x = y`), matching Lean 4.
    let mut env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let z = Expr::const_(Name::from_string("z"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("xy"),
        level_params: vec![],
        type_: make_eq_n(x.clone(), y.clone()),
    })
    .unwrap();

    let target = make_p(x.clone());
    let mut state = ProofState::with_context(
        env,
        target,
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "xy".to_string(),
            ty: make_eq_n(x, z.clone()), // local: x = z
            value: None,
        }],
    );

    rewrite_ltr(&mut state, "xy").expect("local hyp xy should be used");
    assert_eq!(
        state.current_goal().unwrap().target,
        make_p(z),
        "local hyp (x=z) should shadow env const (x=y): goal should be P(z)"
    );
}

#[test]
fn test_rewrite_env_const_no_match_errors() {
    // Env const exists and is an equality, but its LHS does not occur in the goal.
    let mut env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let z = Expr::const_(Name::from_string("z"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("yz"),
        level_params: vec![],
        type_: make_eq_n(y, z),
    })
    .unwrap();

    let mut state = ProofState::new(env, make_p(x));
    let result = rewrite_ltr(&mut state, "yz");
    assert!(
        matches!(result, Err(TacticError::RewriteNoMatch { .. })),
        "env const whose LHS is absent should be RewriteNoMatch, got {result:?}"
    );
}

// ==========================================================================
// rewrite_chain tests
// ==========================================================================

#[test]
fn test_rewrite_chain_two_steps() {
    let env = setup_env_with_full_eq();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let z = Expr::const_(Name::from_string("z"), vec![]);

    // Goal: P(x)
    // h1 : x = y, h2 : y = z
    let target = make_p(x.clone());
    let h1_ty = make_eq_n(x.clone(), y.clone());
    let h2_ty = make_eq_n(y.clone(), z.clone());

    let mut state = ProofState::with_context(
        env,
        target,
        vec![
            LocalDecl {
                fvar: FVarId::new(0),
                name: "h1".to_string(),
                ty: h1_ty,
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(1),
                name: "h2".to_string(),
                ty: h2_ty,
                value: None,
            },
        ],
    );

    // rw [h1, h2] should transform P(x) → P(y) → P(z)
    let result = rewrite_chain(
        &mut state,
        &[
            ("h1", RewriteDirection::Forward),
            ("h2", RewriteDirection::Forward),
        ],
    );
    assert!(result.is_ok(), "rewrite_chain should succeed");

    let new_goal = state.current_goal().unwrap();
    let expected = make_p(z);
    assert_eq!(
        new_goal.target, expected,
        "goal should be P(z) after chain rewrite"
    );
}

#[test]
fn test_rewrite_chain_mixed_directions() {
    let env = setup_env_with_full_eq();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let z = Expr::const_(Name::from_string("z"), vec![]);

    // Goal: P(x)
    // h1 : x = y (forward: x → y)
    // h2 : z = y (backward: y → z)
    let target = make_p(x.clone());
    let h1_ty = make_eq_n(x.clone(), y.clone());
    let h2_ty = make_eq_n(z.clone(), y.clone());

    let mut state = ProofState::with_context(
        env,
        target,
        vec![
            LocalDecl {
                fvar: FVarId::new(0),
                name: "h1".to_string(),
                ty: h1_ty,
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(1),
                name: "h2".to_string(),
                ty: h2_ty,
                value: None,
            },
        ],
    );

    // rw [h1, ←h2]: P(x) → P(y) → P(z)
    let result = rewrite_chain(
        &mut state,
        &[
            ("h1", RewriteDirection::Forward),
            ("h2", RewriteDirection::Backward),
        ],
    );
    assert!(result.is_ok(), "mixed direction chain should succeed");

    let new_goal = state.current_goal().unwrap();
    let expected = make_p(z);
    assert_eq!(
        new_goal.target, expected,
        "goal should be P(z) after mixed chain"
    );
}

#[test]
fn test_rewrite_chain_empty_is_noop() {
    let env = setup_env_with_full_eq();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let target = make_p(x.clone());

    let mut state = ProofState::new(env, target.clone());

    // Empty chain should succeed without changing anything
    let result = rewrite_chain(&mut state, &[]);
    assert!(result.is_ok(), "empty chain should succeed");

    let goal = state.current_goal().unwrap();
    assert_eq!(goal.target, target, "goal should be unchanged");
}

#[test]
fn test_rewrite_chain_fails_on_second_step() {
    let env = setup_env_with_full_eq();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let z = Expr::const_(Name::from_string("z"), vec![]);

    // Goal: P(x)
    // h1 : x = y (matches goal)
    // h2 : z = x (after h1, goal is P(y) — z is not in P(y), forward fails)
    let target = make_p(x.clone());
    let h1_ty = make_eq_n(x.clone(), y.clone());
    let h2_ty = make_eq_n(z.clone(), x.clone());

    let mut state = ProofState::with_context(
        env,
        target,
        vec![
            LocalDecl {
                fvar: FVarId::new(0),
                name: "h1".to_string(),
                ty: h1_ty,
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(1),
                name: "h2".to_string(),
                ty: h2_ty,
                value: None,
            },
        ],
    );

    // h1 succeeds (x→y), h2 fails (z not in P(y))
    let result = rewrite_chain(
        &mut state,
        &[
            ("h1", RewriteDirection::Forward),
            ("h2", RewriteDirection::Forward),
        ],
    );
    assert!(result.is_err(), "chain should fail on non-matching step");
}

// ==========================================================================
// subst tactic tests
// ==========================================================================

#[test]
fn test_subst_eliminates_variable_lhs() {
    let env = setup_env_with_full_eq();

    let n_ty = Expr::const_(Name::from_string("N"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);

    // x : N as an fvar, h : x = y, goal: P(x)
    let x_fvar = FVarId::new(10);
    let target = make_p(Expr::fvar(x_fvar));
    let h_ty = make_eq_n(Expr::fvar(x_fvar), y.clone());

    let mut state = ProofState::with_context(
        env,
        target,
        vec![
            LocalDecl {
                fvar: x_fvar,
                name: "x".to_string(),
                ty: n_ty,
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(11),
                name: "h".to_string(),
                ty: h_ty,
                value: None,
            },
        ],
    );

    let result = subst(&mut state, "h");
    assert!(result.is_ok(), "subst should succeed: {:?}", result.err());

    // After subst, x and h should be removed from context
    let new_goal = state.current_goal().unwrap();
    assert!(
        !new_goal.local_ctx.iter().any(|d| d.name == "x"),
        "x should be removed from context after subst"
    );
    assert!(
        !new_goal.local_ctx.iter().any(|d| d.name == "h"),
        "h should be removed from context after subst"
    );

    // Goal should become P(y) (x replaced by y)
    let expected = make_p(y);
    assert_eq!(
        new_goal.target, expected,
        "goal should have x replaced with y"
    );
}

#[test]
fn test_subst_eliminates_variable_rhs() {
    let env = setup_env_with_full_eq();

    let n_ty = Expr::const_(Name::from_string("N"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);

    // x : N as an fvar, h : y = x, goal: P(x)
    let x_fvar = FVarId::new(10);
    let target = make_p(Expr::fvar(x_fvar));
    let h_ty = make_eq_n(y.clone(), Expr::fvar(x_fvar));

    let mut state = ProofState::with_context(
        env,
        target,
        vec![
            LocalDecl {
                fvar: x_fvar,
                name: "x".to_string(),
                ty: n_ty,
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(11),
                name: "h".to_string(),
                ty: h_ty,
                value: None,
            },
        ],
    );

    let result = subst(&mut state, "h");
    assert!(
        result.is_ok(),
        "subst with fvar on RHS should succeed: {:?}",
        result.err()
    );

    let new_goal = state.current_goal().unwrap();
    assert!(
        !new_goal.local_ctx.iter().any(|d| d.name == "x"),
        "x should be removed"
    );
    assert!(
        !new_goal.local_ctx.iter().any(|d| d.name == "h"),
        "h should be removed"
    );

    let expected = make_p(y);
    assert_eq!(
        new_goal.target, expected,
        "goal should have x replaced with y"
    );
}

#[test]
fn test_subst_replaces_in_other_hypotheses() {
    let env = setup_env_with_full_eq();

    let n_ty = Expr::const_(Name::from_string("N"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);

    // x : N, h : x = y, h2 : P(x), goal: P(x)
    let x_fvar = FVarId::new(10);
    let target = make_p(Expr::fvar(x_fvar));
    let h_ty = make_eq_n(Expr::fvar(x_fvar), y.clone());
    let h2_ty = make_p(Expr::fvar(x_fvar));

    let mut state = ProofState::with_context(
        env,
        target,
        vec![
            LocalDecl {
                fvar: x_fvar,
                name: "x".to_string(),
                ty: n_ty,
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(11),
                name: "h".to_string(),
                ty: h_ty,
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(12),
                name: "h2".to_string(),
                ty: h2_ty,
                value: None,
            },
        ],
    );

    let result = subst(&mut state, "h");
    assert!(result.is_ok(), "subst should succeed");

    let new_goal = state.current_goal().unwrap();

    // h2 should now have type P(y) instead of P(x)
    let h2_decl = new_goal
        .local_ctx
        .iter()
        .find(|d| d.name == "h2")
        .expect("h2 should remain in context");
    let expected_h2_ty = make_p(y);
    assert_eq!(
        h2_decl.ty, expected_h2_ty,
        "h2 type should have x replaced with y"
    );
}

#[test]
fn test_subst_non_variable_fails() {
    let env = setup_env_with_full_eq();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);

    // h : x = y where both x and y are constants (not free variables in context)
    let target = make_p(x.clone());
    let h_ty = make_eq_n(x, y);

    let mut state = ProofState::with_context(
        env,
        target,
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: h_ty,
            value: None,
        }],
    );

    let result = subst(&mut state, "h");
    assert!(
        result.is_err(),
        "subst should fail when neither side is a free variable in context"
    );
}

#[test]
fn test_subst_hypothesis_not_found() {
    let env = setup_env_with_full_eq();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let target = make_p(x);

    let mut state = ProofState::new(env, target);

    let result = subst(&mut state, "nonexistent");
    assert!(
        matches!(result, Err(TacticError::HypothesisNotFound(name)) if name == "nonexistent"),
        "subst should fail with HypothesisNotFound"
    );
}

#[test]
fn test_subst_non_equality_fails() {
    let env = setup_env_with_full_eq();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let target = make_p(x.clone());
    let h_ty = make_p(x); // P(x), not an equality

    let mut state = ProofState::with_context(
        env,
        target,
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: h_ty,
            value: None,
        }],
    );

    let result = subst(&mut state, "h");
    assert!(
        result.is_err(),
        "subst with non-equality hypothesis should fail"
    );
}

// ==========================================================================
// subst_vars tests
// ==========================================================================

#[test]
fn test_subst_vars_eliminates_all_equalities() {
    let env = setup_env_with_full_eq();

    let n_ty = Expr::const_(Name::from_string("N"), vec![]);
    let z = Expr::const_(Name::from_string("z"), vec![]);

    // x : N, y : N, h1 : x = y, h2 : y = z
    // goal: P(x)
    let x_fvar = FVarId::new(10);
    let y_fvar = FVarId::new(11);
    let target = make_p(Expr::fvar(x_fvar));
    let h1_ty = make_eq_n(Expr::fvar(x_fvar), Expr::fvar(y_fvar));
    let h2_ty = make_eq_n(Expr::fvar(y_fvar), z.clone());

    let mut state = ProofState::with_context(
        env,
        target,
        vec![
            LocalDecl {
                fvar: x_fvar,
                name: "x".to_string(),
                ty: n_ty.clone(),
                value: None,
            },
            LocalDecl {
                fvar: y_fvar,
                name: "y".to_string(),
                ty: n_ty,
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(12),
                name: "h1".to_string(),
                ty: h1_ty,
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(13),
                name: "h2".to_string(),
                ty: h2_ty,
                value: None,
            },
        ],
    );

    let result = subst_vars(&mut state);
    assert!(
        result.is_ok(),
        "subst_vars should succeed: {:?}",
        result.err()
    );

    // Both x and y should be eliminated
    let new_goal = state.current_goal().unwrap();
    assert!(
        !new_goal.local_ctx.iter().any(|d| d.name == "x"),
        "x should be removed by subst_vars"
    );
    assert!(
        !new_goal.local_ctx.iter().any(|d| d.name == "h1"),
        "h1 should be removed by subst_vars"
    );
}

#[test]
fn test_subst_vars_no_equalities_is_noop() {
    let env = setup_env_with_full_eq();

    let x = Expr::const_(Name::from_string("x"), vec![]);
    let target = make_p(x.clone());
    let h_ty = make_p(x); // Not an equality

    let mut state = ProofState::with_context(
        env,
        target.clone(),
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: h_ty,
            value: None,
        }],
    );

    let result = subst_vars(&mut state);
    assert!(
        result.is_ok(),
        "subst_vars with no equalities should succeed"
    );

    // Goal should be unchanged
    let new_goal = state.current_goal().unwrap();
    assert_eq!(new_goal.target, target, "goal should be unchanged");
}

// ==========================================================================
// Global-lemma rw: end-to-end surface dispatch + negative teeth + chained
// global/local. These complement the `rewrite_ltr`-level env tests above by
// driving the FULL surface path (`SurfaceTactic::Rw` -> compound `rw` handler
// -> rw_goal_rules -> rewrite_ltr) and by pinning the clean-failure contract
// for unknown / non-equation rule identifiers.
// ==========================================================================

/// Drive the registry-level `rw` compound handler exactly as the parser would
/// for surface `rw [<rules>]` on the goal. Returns the handler result so
/// negative tests can inspect the error.
fn run_surface_rw(state: &mut ProofState, rules: &[(&str, bool)]) -> Result<(), TacticError> {
    use crate::tactic::builtins::register_builtin_tactics;
    use crate::tactic::builtins_phase3d_rewrite::register_phase3d_rewrite;
    use crate::tactic::registry::{ElaboratedRefine, TacticEval, TacticRegistry};
    use crate::unify::MetaState;
    use clean_parser::{Span, SurfaceExpr, SurfaceRwRule, SurfaceTactic, SurfaceTacticLocation};

    // A `TacticEval` that refuses recursion/elaboration: the name-keyed global
    // path must NOT need it, so any call signals the test took the wrong branch.
    struct NoopEval {
        metas: MetaState,
    }
    impl TacticEval for NoopEval {
        fn eval(&mut self, _ps: &mut ProofState, _t: &SurfaceTactic) -> Result<(), TacticError> {
            Ok(())
        }
        fn eval_seq(
            &mut self,
            _ps: &mut ProofState,
            _t: &[SurfaceTactic],
        ) -> Result<(), TacticError> {
            Ok(())
        }
        fn elaborate(&mut self, _e: &SurfaceExpr) -> Result<Expr, TacticError> {
            panic!("global-lemma rw must resolve by name, not elaborate a proof term")
        }
        fn infer_type(&mut self, _e: &Expr) -> Result<Expr, TacticError> {
            panic!("global-lemma rw must not infer_type")
        }
        fn elaborate_refine(
            &mut self,
            _ps: &ProofState,
            _e: &SurfaceExpr,
        ) -> Result<ElaboratedRefine, TacticError> {
            panic!("global-lemma rw must not elaborate_refine")
        }
        fn metas(&self) -> &MetaState {
            &self.metas
        }
    }

    let mut registry = TacticRegistry::new();
    register_builtin_tactics(&mut registry);
    register_phase3d_rewrite(&mut registry);
    let rw = registry
        .get_compound("rw")
        .expect("rw should be registered as a compound tactic");
    let surface_rules: Vec<SurfaceRwRule> = rules
        .iter()
        .map(|(name, reverse)| SurfaceRwRule {
            span: Span::dummy(),
            reverse: *reverse,
            term: SurfaceExpr::Ident(Span::dummy(), (*name).to_string()),
        })
        .collect();
    let tactic = SurfaceTactic::Rw(Span::dummy(), surface_rules, SurfaceTacticLocation::Goal);
    let mut eval = NoopEval {
        metas: MetaState::new(),
    };
    (rw.handler)(&mut eval, state, &tactic)
}

#[test]
fn test_surface_rw_global_lemma_end_to_end_rewrites_and_checks() {
    // End-to-end through the SAME dispatch the parser uses for `rw [gx]`:
    // SurfaceTactic::Rw -> compound `rw` -> rw_goal_rules -> rewrite_ltr -> env
    // fallback. `gx : ∀ (a : N), g a = a`; goal `P (g x)` must become `P x`,
    // and the assembled Eq.subst proof must kernel-type-check.
    let env = setup_env_with_g();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let g = Expr::const_(Name::from_string("g"), vec![]);
    let g_a = Expr::app(g.clone(), Expr::bvar(0));
    let gx_ty = Expr::pi(
        BinderInfo::Default,
        Expr::const_(Name::from_string("N"), vec![]),
        make_eq_n(g_a, Expr::bvar(0)),
    );
    let mut env = env;
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("gx"),
        level_params: vec![],
        type_: gx_ty,
    })
    .unwrap();

    let target = make_p(Expr::app(g, x.clone()));
    let mut state = ProofState::new(env, target.clone());
    let root = state.current_goal().unwrap().meta_id;

    run_surface_rw(&mut state, &[("gx", false)])
        .expect("surface rw [gx] should resolve the global lemma and rewrite");

    assert_eq!(
        state.current_goal().unwrap().target,
        make_p(x),
        "surface rw [gx] should rewrite P (g x) -> P x"
    );
    assert_root_proof_checks(&state, root, &target);
}

#[test]
fn test_surface_rw_chained_global_then_local_rewrites_and_checks() {
    // Chained `rw [gx, h]` mixing a GLOBAL lemma and a LOCAL hypothesis, the
    // `rw [Nat.add_succ, ih]`-style induction-step shape:
    //   gx : ∀ (a : N), g a = a   (global)
    //   h  : x = y                (local hyp)
    //   goal: P (g x)  --gx-->  P x  --h-->  P y
    let env = setup_env_with_g();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let g = Expr::const_(Name::from_string("g"), vec![]);
    let g_a = Expr::app(g.clone(), Expr::bvar(0));
    let gx_ty = Expr::pi(
        BinderInfo::Default,
        Expr::const_(Name::from_string("N"), vec![]),
        make_eq_n(g_a, Expr::bvar(0)),
    );
    let mut env = env;
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("gx"),
        level_params: vec![],
        type_: gx_ty,
    })
    .unwrap();

    let target = make_p(Expr::app(g, x.clone()));
    let mut state = ProofState::with_context(
        env,
        target.clone(),
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: make_eq_n(x.clone(), y.clone()),
            value: None,
        }],
    );
    let root = state.current_goal().unwrap().meta_id;

    run_surface_rw(&mut state, &[("gx", false), ("h", false)])
        .expect("chained rw [gx, h] (global then local) should both fire");

    assert_eq!(
        state.current_goal().unwrap().target,
        make_p(y),
        "chained rw should rewrite P (g x) -> P x -> P y"
    );
    assert_root_proof_checks(&state, root, &target);
}

#[test]
fn test_surface_rw_unknown_global_fails_clean_not_found() {
    // NEGATIVE: `rw [NoSuchLemma]` — neither local hyp nor env const — must
    // surface a clean HypothesisNotFound naming the missing identifier, never
    // a panic / crash.
    let env = setup_env_with_full_eq();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let mut state = ProofState::new(env, make_p(x));

    let result = run_surface_rw(&mut state, &[("NoSuchLemma", false)]);
    assert!(
        matches!(result, Err(TacticError::HypothesisNotFound(ref n)) if n == "NoSuchLemma"),
        "rw [NoSuchLemma] should be a clean HypothesisNotFound, got {result:?}"
    );
}

#[test]
fn test_rewrite_env_const_non_equation_fails_clean() {
    // NEGATIVE/teeth: a global constant that is NOT an equation (here a plain
    // function `g : N -> N`, the kind a user might fat-finger as `rw [g]`) must
    // fail with a clear "not an equation" diagnostic — never a bogus rewrite.
    // After peeling its leading Pi binder the body is `N` (not `@Eq …`), so
    // resolution rejects it cleanly.
    let env = setup_env_with_g();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let g = Expr::const_(Name::from_string("g"), vec![]);
    let target = make_p(Expr::app(g, x.clone()));
    let mut state = ProofState::new(env, target.clone());

    let result = rewrite_ltr(&mut state, "g");
    match result {
        Err(TacticError::GoalMismatch(msg)) => {
            assert!(
                msg.contains("not an equation") && msg.contains('g'),
                "non-equation rule error should name the rule and say 'not an equation', got: {msg}"
            );
        }
        other => {
            panic!("rw [g] on a non-equation global should be a clean GoalMismatch, got {other:?}")
        }
    }
    // Teeth: the goal must be COMPLETELY UNCHANGED (no partial / bogus rewrite).
    assert_eq!(
        state.current_goal().unwrap().target,
        target,
        "a rejected non-equation rule must leave the goal untouched"
    );
}

#[test]
fn test_surface_rw_non_equation_global_fails_clean() {
    // Same teeth as above but through the FULL surface dispatch path.
    let env = setup_env_with_g();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let g = Expr::const_(Name::from_string("g"), vec![]);
    let target = make_p(Expr::app(g, x.clone()));
    let mut state = ProofState::new(env, target.clone());

    let result = run_surface_rw(&mut state, &[("g", false)]);
    assert!(
        matches!(result, Err(TacticError::GoalMismatch(ref m)) if m.contains("not an equation")),
        "surface rw [g] on a non-equation global should be a clean GoalMismatch, got {result:?}"
    );
    assert_eq!(
        state.current_goal().unwrap().target,
        target,
        "rejected surface rw must leave the goal untouched"
    );
}

// ==========================================================================
// `rw [<proof-term>] at h` — rewrite_at_with_proof (applied / non-identifier
// rule terms inside a hypothesis, the at-hyp analogue of rewrite_with_proof)
// ==========================================================================

#[test]
fn test_rewrite_at_with_proof_applied_lemma_rewrites_hyp_and_checks() {
    // `rw [gx x] at h`: rewrite a hypothesis by an *applied* proof term — a
    // non-identifier the name-keyed at-hyp path can't take. gx : ∀ a, g a = a,
    // so `gx x : g x = x`; hyp `h : P (g x)` must become `P x`. Then close the
    // goal `P x` by the rewritten `h` and kernel-check the whole assembled
    // proof (which embeds the `Eq.subst` cast the rewrite produced).
    let mut env = setup_env_with_g();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let g = Expr::const_(Name::from_string("g"), vec![]);
    let g_a = Expr::app(g.clone(), Expr::bvar(0));
    let gx_ty = Expr::pi(
        BinderInfo::Default,
        Expr::const_(Name::from_string("N"), vec![]),
        make_eq_n(g_a, Expr::bvar(0)),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("gx"),
        level_params: vec![],
        type_: gx_ty,
    })
    .unwrap();

    let target = make_p(x.clone());
    let hyp_ty = make_p(Expr::app(g.clone(), x.clone()));
    let mut state = ProofState::with_context(
        env,
        target.clone(),
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: hyp_ty,
            value: None,
        }],
    );
    let orig_goal = state.current_goal().unwrap().clone();

    // Proof term `gx x : g x = x` — an application, NOT a bare identifier.
    let gx_x = Expr::app(Expr::const_(Name::from_string("gx"), vec![]), x.clone());
    rewrite_at_with_proof(&mut state, gx_x.clone(), "h", false)
        .expect("rw [gx x] at h should rewrite P (g x) -> P x");

    let goal_after = state.current_goal().unwrap().clone();
    let h_decl = goal_after
        .local_ctx
        .iter()
        .find(|d| d.name == "h")
        .expect("h must survive the rewrite");
    let rewritten_hyp_ty = make_p(x.clone());
    assert_eq!(
        h_decl.ty, rewritten_hyp_ty,
        "rw [gx x] at h should rewrite the hypothesis P (g x) -> P x"
    );
    // The at-hyp rewrite never touches the goal target.
    assert_eq!(
        goal_after.target, target,
        "rw [gx x] at h must leave the goal target unchanged"
    );

    // Independent kernel re-check: the forward `Eq.subst` cast
    // `Eq.subst N (fun t => P t) (g x) x (gx x) h` proves exactly `P x`.
    assert_eq_subst_cast_checks(
        &state,
        &orig_goal,
        Expr::app(g.clone(), x.clone()),
        x.clone(),
        gx_x,
        FVarId::new(0),
        &rewritten_hyp_ty,
    );
}

#[test]
fn test_rewrite_at_with_proof_reverse_uses_eq_symm_and_checks() {
    // `rw [← gx x] at h`: REVERSE rewrite of a hypothesis by an applied term,
    // exercising the `Eq.symm` branch. gx x : g x = x, so the reverse rule
    // rewrites the RHS `x` back to the LHS `g x`: hyp `h : P x` -> `P (g x)`.
    let mut env = setup_env_with_g();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let g = Expr::const_(Name::from_string("g"), vec![]);
    let g_a = Expr::app(g.clone(), Expr::bvar(0));
    let gx_ty = Expr::pi(
        BinderInfo::Default,
        Expr::const_(Name::from_string("N"), vec![]),
        make_eq_n(g_a, Expr::bvar(0)),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("gx"),
        level_params: vec![],
        type_: gx_ty,
    })
    .unwrap();

    let target = make_p(Expr::app(g.clone(), x.clone()));
    let hyp_ty = make_p(x.clone());
    let mut state = ProofState::with_context(
        env,
        target.clone(),
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: hyp_ty,
            value: None,
        }],
    );
    let orig_goal = state.current_goal().unwrap().clone();

    let gx_x = Expr::app(Expr::const_(Name::from_string("gx"), vec![]), x.clone());
    rewrite_at_with_proof(&mut state, gx_x.clone(), "h", true)
        .expect("rw [← gx x] at h should rewrite P x -> P (g x)");

    let goal_after = state.current_goal().unwrap().clone();
    let h_decl = goal_after
        .local_ctx
        .iter()
        .find(|d| d.name == "h")
        .expect("h must survive the reverse rewrite");
    let rewritten_hyp_ty = make_p(Expr::app(g.clone(), x.clone()));
    assert_eq!(
        h_decl.ty, rewritten_hyp_ty,
        "reverse rw [← gx x] at h should rewrite P x -> P (g x)"
    );
    assert_eq!(
        goal_after.target, target,
        "reverse rw [← gx x] at h must leave the goal target unchanged"
    );

    // Independent kernel re-check of the REVERSE cast: the rewrite flips the
    // equation with `Eq.symm (gx x) : x = g x`, so
    // `Eq.subst N (fun t => P t) x (g x) (Eq.symm (gx x)) h` proves `P (g x)`.
    let eq_symm = Expr::const_(
        Name::from_string("Eq.symm"),
        vec![Level::succ(Level::zero())],
    );
    let symm_proof = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(eq_symm, Expr::const_(Name::from_string("N"), vec![])),
                Expr::app(g.clone(), x.clone()),
            ),
            x.clone(),
        ),
        gx_x,
    );
    assert_eq_subst_cast_checks(
        &state,
        &orig_goal,
        x.clone(),
        Expr::app(g.clone(), x.clone()),
        symm_proof,
        FVarId::new(0),
        &rewritten_hyp_ty,
    );
}

#[test]
fn test_rewrite_at_with_proof_no_match_errors_clean_and_preserves_hyp() {
    // NEGATIVE: `rw [gx x] at h` where the LHS `g x` does NOT occur in the
    // hypothesis `h : P y` must surface a clean `RewriteNoMatch` (never a panic)
    // and leave the hypothesis byte-for-byte untouched.
    let mut env = setup_env_with_g();
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let g = Expr::const_(Name::from_string("g"), vec![]);
    let g_a = Expr::app(g.clone(), Expr::bvar(0));
    let gx_ty = Expr::pi(
        BinderInfo::Default,
        Expr::const_(Name::from_string("N"), vec![]),
        make_eq_n(g_a, Expr::bvar(0)),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("gx"),
        level_params: vec![],
        type_: gx_ty,
    })
    .unwrap();

    let hyp_ty = make_p(y.clone());
    let mut state = ProofState::with_context(
        env,
        make_p(x.clone()),
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: hyp_ty.clone(),
            value: None,
        }],
    );

    let proof = Expr::app(Expr::const_(Name::from_string("gx"), vec![]), x.clone());
    let result = rewrite_at_with_proof(&mut state, proof, "h", false);
    assert!(
        matches!(result, Err(TacticError::RewriteNoMatch { .. })),
        "rw [gx x] at h with no occurrence of `g x` in h should be a clean \
         RewriteNoMatch, got {result:?}"
    );
    // Teeth: the hypothesis must be completely unchanged.
    let h_decl = state
        .current_goal()
        .unwrap()
        .local_ctx
        .iter()
        .find(|d| d.name == "h")
        .expect("h must still be present after a rejected rewrite");
    assert_eq!(
        h_decl.ty, hyp_ty,
        "a rejected rw [_] at h must leave the hypothesis untouched"
    );
}
