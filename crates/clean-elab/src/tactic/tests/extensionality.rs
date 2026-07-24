// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extensionality tactics: funext, ext, ext_multi, congr_depth, ExtConfig.
//!
//! Part of #3082: validates function extensionality, multi-arg ext, and
//! depth-controlled congruence for equality goals.

use super::*;
use clean_kernel::env::Declaration;

// ---------------------------------------------------------------------------
// Environment setup helpers
// ---------------------------------------------------------------------------

/// Environment with Eq + funext + type A + functions f,g : A → A.
fn setup_env_with_funext() -> Environment {
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_funext().unwrap();

    let a_ty = Expr::type_();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: a_ty,
    })
    .unwrap();

    let a = Expr::const_(Name::from_string("A"), vec![]);

    // f : A → A
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("f"),
        level_params: vec![],
        type_: Expr::arrow(a.clone(), a.clone()),
    })
    .unwrap();

    // g : A → A
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("g"),
        level_params: vec![],
        type_: Expr::arrow(a.clone(), a.clone()),
    })
    .unwrap();

    env
}

/// Environment with Eq + funext + type A + curried functions h,k : A → A → A.
fn setup_env_with_funext_multi() -> Environment {
    let mut env = setup_env_with_funext();

    let a = Expr::const_(Name::from_string("A"), vec![]);
    let aa = Expr::arrow(a.clone(), a.clone());
    let aaa = Expr::arrow(a.clone(), aa);

    // h : A → A → A
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("h"),
        level_params: vec![],
        type_: aaa.clone(),
    })
    .unwrap();

    // k : A → A → A
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("k"),
        level_params: vec![],
        type_: aaa,
    })
    .unwrap();

    env
}

/// Environment with Eq + congrArg + type A + function f : A → A + constants a,b : A.
fn setup_env_with_congr() -> Environment {
    let mut env = Environment::new();
    env.init_eq().unwrap();

    let a_ty = Expr::type_();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: a_ty,
    })
    .unwrap();

    let a = Expr::const_(Name::from_string("A"), vec![]);

    // f : A → A
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("f"),
        level_params: vec![],
        type_: Expr::arrow(a.clone(), a.clone()),
    })
    .unwrap();

    // a : A
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("a"),
        level_params: vec![],
        type_: a.clone(),
    })
    .unwrap();

    // b : A
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("b"),
        level_params: vec![],
        type_: a.clone(),
    })
    .unwrap();

    env
}

// ---------------------------------------------------------------------------
// ExtConfig construction tests
// ---------------------------------------------------------------------------

#[test]
fn test_ext_config_default() {
    let config = ExtConfig::default();
    assert!(config.names.is_empty(), "default config has no names");
    assert!(config.depth.is_none(), "default config has no depth");
}

#[test]
fn test_ext_config_with_name() {
    let config = ExtConfig::with_name("x");
    assert_eq!(config.names.len(), 1);
    assert_eq!(config.names[0].as_deref(), Some("x"));
    assert!(config.depth.is_none());
}

#[test]
fn test_ext_config_with_names() {
    let config = ExtConfig::with_names(&["x", "y"]);
    assert_eq!(config.names.len(), 2);
    assert_eq!(config.names[0].as_deref(), Some("x"));
    assert_eq!(config.names[1].as_deref(), Some("y"));
}

#[test]
fn test_ext_config_auto_names() {
    let config = ExtConfig::auto_names(3);
    assert_eq!(config.names.len(), 3);
    for name in &config.names {
        assert!(name.is_none(), "auto names should all be None");
    }
}

#[test]
fn test_ext_config_with_depth() {
    let config = ExtConfig::with_depth(2);
    assert!(config.names.is_empty());
    assert_eq!(config.depth, Some(2));
}

// ---------------------------------------------------------------------------
// funext tests
// ---------------------------------------------------------------------------

#[test]
fn test_funext_introduces_var() {
    let env = setup_env_with_funext();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let g = Expr::const_(Name::from_string("g"), vec![]);

    // Goal: f = g where f g : A → A
    let target = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                Expr::arrow(a.clone(), a.clone()),
            ),
            f,
        ),
        g,
    );

    let mut state = ProofState::new(env, target);
    let result = funext(&mut state, "x");
    assert!(result.is_ok(), "funext should succeed: {result:?}");

    // After funext, there should be a goal with x in context
    let goal = state
        .current_goal()
        .expect("should have a goal after funext");
    let has_x = goal.local_ctx.iter().any(|d| d.name == "x");
    assert!(has_x, "funext should introduce variable 'x' into context");
}

#[test]
fn test_funext_non_function_fails() {
    let env = setup_env_with_funext();
    let a = Expr::const_(Name::from_string("A"), vec![]);

    // Goal: A = A (not a function equality)
    let target = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Eq"),
                    vec![Level::succ(Level::succ(Level::zero()))],
                ),
                Expr::type_(),
            ),
            a.clone(),
        ),
        a.clone(),
    );

    let mut state = ProofState::new(env, target);
    let result = funext(&mut state, "x");
    assert!(
        result.is_err(),
        "funext should fail on non-function equality"
    );
}

// ---------------------------------------------------------------------------
// ext (single-arg, from generalize.rs) tests
// ---------------------------------------------------------------------------

#[test]
fn test_ext_function_equality() {
    let env = setup_env_with_funext();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let g = Expr::const_(Name::from_string("g"), vec![]);

    // Goal: f = g where f g : A → A
    let target = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                Expr::arrow(a.clone(), a.clone()),
            ),
            f,
        ),
        g,
    );

    let mut state = ProofState::new(env, target);
    let result = ext(&mut state, "n");
    assert!(result.is_ok(), "ext should succeed on f = g: {result:?}");

    let goal = state.current_goal().expect("should have goal after ext");
    let has_n = goal.local_ctx.iter().any(|d| d.name == "n");
    assert!(has_n, "ext should introduce variable 'n'");
}

// ---------------------------------------------------------------------------
// ext_multi tests
// ---------------------------------------------------------------------------

#[test]
fn test_ext_multi_auto_name() {
    let env = setup_env_with_funext();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let g = Expr::const_(Name::from_string("g"), vec![]);

    let target = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                Expr::arrow(a.clone(), a.clone()),
            ),
            f,
        ),
        g,
    );

    let mut state = ProofState::new(env, target);
    let config = ExtConfig::default(); // empty names → auto-generate one
    let result = ext_multi(&mut state, &config);
    assert!(
        result.is_ok(),
        "ext_multi with auto name should succeed: {result:?}"
    );

    let goal = state.current_goal().expect("should have goal");
    let has_x = goal.local_ctx.iter().any(|d| d.name == "x");
    assert!(has_x, "auto-named ext should introduce 'x'");
}

#[test]
fn test_ext_multi_multiple_args() {
    let env = setup_env_with_funext_multi();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let h = Expr::const_(Name::from_string("h"), vec![]);
    let k = Expr::const_(Name::from_string("k"), vec![]);

    // h k : A → A → A
    // Goal: h = k
    let aa = Expr::arrow(a.clone(), a.clone());
    let fn_ty = Expr::arrow(a.clone(), aa);
    let target = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                fn_ty,
            ),
            h,
        ),
        k,
    );

    let mut state = ProofState::new(env, target);
    let config = ExtConfig::with_names(&["x", "y"]);
    let result = ext_multi(&mut state, &config);
    assert!(
        result.is_ok(),
        "ext_multi x y should succeed on curried function equality: {result:?}"
    );

    // After two ext applications, both x and y should be in context
    let goal = state
        .current_goal()
        .expect("should have goal after ext_multi");
    let has_x = goal.local_ctx.iter().any(|d| d.name == "x");
    let has_y = goal.local_ctx.iter().any(|d| d.name == "y");
    assert!(has_x, "ext_multi should introduce 'x'");
    assert!(has_y, "ext_multi should introduce 'y'");
}

// ---------------------------------------------------------------------------
// congr tests
// ---------------------------------------------------------------------------

#[test]
fn test_congr_non_equality_fails() {
    let env = setup_env_with_congr();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);

    // Goal is just a type, not an equality -- congr should fail
    let mut state = ProofState::new(env, a_ty);
    let result = congr(&mut state);
    assert!(result.is_err(), "congr should fail on non-equality goal");
}

#[test]
fn test_congr_depth_zero_noop() {
    let env = setup_env_with_congr();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    let target = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                a_ty,
            ),
            Expr::app(f.clone(), a),
        ),
        Expr::app(f, b),
    );

    let mut state = ProofState::new(env, target);
    let goals_before = state.goals().len();
    let result = congr_depth(&mut state, 0);
    assert!(result.is_ok(), "congr_depth 0 should be a no-op");
    assert_eq!(
        state.goals().len(),
        goals_before,
        "congr_depth 0 should not change goal count"
    );
}

#[test]
fn test_congr_depth_zero_with_config() {
    let env = setup_env_with_congr();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    // Goal: a = a (rfl-solvable, but congr at depth 0 should be a no-op)
    let target = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                a_ty,
            ),
            a.clone(),
        ),
        a,
    );

    let mut state = ProofState::new(env, target);
    let config = ExtConfig::with_depth(0);
    let goals_before = state.goals().len();
    let result = congr_with_config(&mut state, &config);
    assert!(result.is_ok(), "congr_with_config at depth 0 is a no-op");
    assert_eq!(
        state.goals().len(),
        goals_before,
        "congr_with_config at depth 0 should not change goals"
    );
}

#[test]
fn test_congr_rfl_case() {
    // When both sides are identical (no args), congr falls through to rfl
    let env = setup_env_with_congr();
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    // Goal: a = a
    let target = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                a_ty,
            ),
            a.clone(),
        ),
        a,
    );

    let mut state = ProofState::new(env, target);
    let result = congr(&mut state);
    assert!(
        result.is_ok(),
        "congr on a = a should succeed via rfl: {result:?}"
    );
    // rfl closes the goal entirely
    assert!(
        state.goals().is_empty(),
        "congr on a = a should close the goal via rfl"
    );
}

// ---------------------------------------------------------------------------
// funext end-to-end kernel-check tests (#2204 FVar-id ↔ binder-depth fix)
//
// The bug: funext wasted an FVar on throwaway universe-level inference before
// its trailing `intro`, so the introduced pointwise binder landed one id past
// the binder depth of the assembled `funext … (fun x => …)` term. `close_fvars`
// could not convert it → `closed_proof()` failed closed → `ProofNotProduced`.
//
// These tests drive the FULL pipeline (funext → solve pointwise → closed_proof
// → kernel check_type), which is what actually regressed. The `introduces_var`
// tests above only checked that a var appears in context, not that the final
// proof term kernel-checks.
// ---------------------------------------------------------------------------

/// Build `@Eq.{u+1} ty lhs rhs`.
fn mk_eq(ty: Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                ty,
            ),
            lhs,
        ),
        rhs,
    )
}

/// funext + `exact h x` on `f = g` (h : ∀ x, f x = g x) must produce a
/// kernel-checkable proof term. This is teeth #1 (positive) at the unit level.
#[test]
fn test_funext_pointwise_exact_kernel_checks() {
    let mut env = setup_env_with_funext();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let g = Expr::const_(Name::from_string("g"), vec![]);

    // h : ∀ x : A, f x = g x  (as an environment axiom so the only FVar in the
    // proof term is funext's introduced binder).
    let fx = Expr::app(f.clone(), Expr::bvar(0));
    let gx = Expr::app(g.clone(), Expr::bvar(0));
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("h"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, a.clone(), mk_eq(a.clone(), fx, gx)),
    })
    .unwrap();

    // Goal: f = g
    let target = mk_eq(Expr::arrow(a.clone(), a.clone()), f, g);
    let mut state = ProofState::new(env.clone(), target.clone());

    funext(&mut state, "x").expect("funext should transform f = g");

    // Solve the pointwise goal `f x = g x` with `h x`.
    let x_fvar = state
        .current_goal()
        .expect("pointwise goal present")
        .local_ctx
        .iter()
        .find(|d| d.name == "x")
        .map(|d| d.fvar)
        .expect("funext introduced x");
    let h = Expr::const_(Name::from_string("h"), vec![]);
    exact(&mut state, Expr::app(h, Expr::fvar(x_fvar))).expect("exact h x should close pointwise");

    assert!(state.is_complete(), "no goals should remain");
    let proof = state
        .closed_proof()
        .expect("funext proof must close (no ID-to-binder gap → not ProofNotProduced)");
    TypeChecker::new(&env)
        .check_type(&proof, &target)
        .expect("kernel must re-check the funext proof term against f = g");
}

/// funext + `rfl` on `(fun x => f x) = f`. Teeth #2 (positive) at the unit
/// level: the pointwise goal `(fun x => f x) x = f x` is rfl-provable.
#[test]
fn test_funext_pointwise_rfl_kernel_checks() {
    let env = setup_env_with_funext();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let f = Expr::const_(Name::from_string("f"), vec![]);

    // eta-expanded lhs: fun x : A => f x
    let eta = Expr::lam(
        BinderInfo::Default,
        a.clone(),
        Expr::app(f.clone(), Expr::bvar(0)),
    );

    // Goal: (fun x => f x) = f
    let target = mk_eq(Expr::arrow(a.clone(), a.clone()), eta, f);
    let mut state = ProofState::new(env.clone(), target.clone());

    funext(&mut state, "x").expect("funext should transform (fun x => f x) = f");
    rfl(&mut state).expect("rfl should close the pointwise goal");

    assert!(state.is_complete(), "no goals should remain");
    let proof = state
        .closed_proof()
        .expect("funext+rfl proof must close (not ProofNotProduced)");
    TypeChecker::new(&env)
        .check_type(&proof, &target)
        .expect("kernel must re-check the funext+rfl proof term");
}

/// Two-argument funext on curried `h = k` (h k : A → A → A). Teeth #3
/// (positive): successive introduced binders must be depth-aligned so the
/// nested `funext … (fun a => funext … (fun b => …))` closes and kernel-checks.
#[test]
fn test_funext_two_arg_kernel_checks() {
    let mut env = setup_env_with_funext_multi();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let h = Expr::const_(Name::from_string("h"), vec![]);
    let k = Expr::const_(Name::from_string("k"), vec![]);

    // hyp : ∀ a b : A, h a b = k a b
    let hab = Expr::app(Expr::app(h.clone(), Expr::bvar(1)), Expr::bvar(0));
    let kab = Expr::app(Expr::app(k.clone(), Expr::bvar(1)), Expr::bvar(0));
    let inner = Expr::pi(BinderInfo::Default, a.clone(), mk_eq(a.clone(), hab, kab));
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("hyp"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, a.clone(), inner),
    })
    .unwrap();

    // Goal: h = k
    let aa = Expr::arrow(a.clone(), a.clone());
    let target = mk_eq(Expr::arrow(a.clone(), aa), h, k);
    let mut state = ProofState::new(env.clone(), target.clone());

    funext(&mut state, "a").expect("first funext");
    funext(&mut state, "b").expect("second funext");

    // Solve `h a b = k a b` with `hyp a b`.
    let goal = state.current_goal().expect("pointwise goal present");
    let a_fvar = goal
        .local_ctx
        .iter()
        .find(|d| d.name == "a")
        .map(|d| d.fvar)
        .expect("a introduced");
    let b_fvar = goal
        .local_ctx
        .iter()
        .find(|d| d.name == "b")
        .map(|d| d.fvar)
        .expect("b introduced");
    let hyp = Expr::const_(Name::from_string("hyp"), vec![]);
    let hyp_ab = Expr::app(Expr::app(hyp, Expr::fvar(a_fvar)), Expr::fvar(b_fvar));
    exact(&mut state, hyp_ab).expect("exact hyp a b should close");

    assert!(state.is_complete(), "no goals should remain");
    let proof = state
        .closed_proof()
        .expect("nested funext proof must close (not ProofNotProduced)");
    TypeChecker::new(&env)
        .check_type(&proof, &target)
        .expect("kernel must re-check the two-arg funext proof term");
}

/// Teeth #4 (must-fail): funext on a NON-function equality must Err with
/// GoalMismatch — never over-accept, never panic.
#[test]
fn test_funext_non_function_errs_goal_mismatch() {
    let env = setup_env_with_funext();
    let a = Expr::const_(Name::from_string("A"), vec![]);

    // Goal: A = A (Sort-level equality, not between functions).
    let target = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("Eq"),
                    vec![Level::succ(Level::succ(Level::zero()))],
                ),
                Expr::type_(),
            ),
            a.clone(),
        ),
        a,
    );
    let mut state = ProofState::new(env, target);
    match funext(&mut state, "x") {
        Err(TacticError::GoalMismatch(_)) => {}
        other => panic!("funext on non-function equality must GoalMismatch, got {other:?}"),
    }
}

/// Teeth #5 (must-fail): funext then `rfl` on `f = g` for arbitrary f, g. The
/// pointwise goal `f x = g x` is NOT rfl-provable; the tactic must Err (rfl
/// fails on the pointwise goal), and no closable proof may be produced.
#[test]
fn test_funext_wrong_pointwise_rfl_errs() {
    let env = setup_env_with_funext();
    let a = Expr::const_(Name::from_string("A"), vec![]);
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let g = Expr::const_(Name::from_string("g"), vec![]);

    // Goal: f = g  (f, g are distinct axioms → f x = g x is not rfl-provable)
    let target = mk_eq(Expr::arrow(a.clone(), a.clone()), f, g);
    let mut state = ProofState::new(env, target);

    funext(&mut state, "x").expect("funext transforms the goal");
    assert!(
        rfl(&mut state).is_err(),
        "rfl must fail on the non-reflexive pointwise goal f x = g x"
    );
    // The pointwise goal is still open → no complete, closable proof.
    assert!(
        !state.is_complete(),
        "state must not be complete when the pointwise goal is unsolved"
    );
}
