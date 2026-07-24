// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::expr::ExprKind;

// Tests for simp tactic

#[test]
fn test_simp_beta_reduction() {
    let mut env = setup_env();
    env.init_eq().unwrap();

    // Goal: (λ x => x) a = a
    // After beta reduction, becomes: a = a, closed by rfl
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    // Create (λ x : A => x) a
    let identity = Expr::lam(BinderInfo::Default, a_ty.clone(), Expr::bvar(0));
    let lhs = Expr::app(identity, a.clone());

    // Build equality goal
    let eq = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                a_ty,
            ),
            lhs,
        ),
        a,
    );

    let mut state = ProofState::new(env, eq);

    // simp should apply beta reduction and close with rfl
    let result = simp_default(&mut state);
    assert!(result.is_ok(), "simp failed: {result:?}");
    assert!(
        state.goals().is_empty(),
        "simp should close beta-reduction goal via rfl, but {} goals remain",
        state.goals().len()
    );
}

#[test]
fn test_simp_no_progress() {
    let env = setup_env();

    // Goal: A (no simplification possible, and can't close with rfl/assumption)
    let target = Expr::const_(Name::from_string("A"), vec![]);

    let mut state = ProofState::new(env, target);

    // simp should fail - no progress and can't close
    let err = simp_default(&mut state).unwrap_err();
    assert!(
        matches!(err, TacticError::NoProgress { .. }),
        "simp on unsimplifiable goal should produce NoProgress, got: {err}"
    );
}

#[test]
fn test_simp_with_assumption() {
    let mut env = setup_env();
    env.init_eq().unwrap();

    // Goal: A (with hypothesis h : A in context)
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);

    // A → A
    let target = Expr::arrow(a_ty.clone(), a_ty);

    let mut state = ProofState::new(env, target);

    // intro h
    intro(&mut state, "h").unwrap();

    // simp should close by assumption
    simp_default(&mut state)
        .expect("simp should close goal by assumption when h : A is in context");
    assert!(state.goals().is_empty());
}

#[test]
fn test_simp_config_default() {
    let config = SimpConfig::new();
    assert_eq!(config.max_steps, 1000);
    assert!(config.beta);
    assert!(config.eta);
    assert!(!config.unfold);
    assert!(config.extra_lemmas.is_empty());
    assert!(config.exclude.is_empty());
}

#[test]
fn test_simp_only_simplify_mode() {
    let mut env = setup_env();
    env.init_eq().unwrap();

    // Goal: A → A
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let target = Expr::arrow(a_ty.clone(), a_ty);

    let mut state = ProofState::new(env, target);
    intro(&mut state, "h").unwrap();

    // With only_simplify=true, should not try to close the goal
    let mut config = SimpConfig::new();
    config.only_simplify = true;

    // Should fail since no simplification happens and we don't try closing tactics
    let err = simp(&mut state, config).unwrap_err();
    assert!(
        matches!(err, TacticError::NoProgress { .. }),
        "simp with only_simplify on non-simplifiable goal should produce NoProgress, got: {err}"
    );
}

// Tests for registered simp lemma support (#1670)

#[test]
fn test_simp_uses_registered_env_lemma() {
    use clean_kernel::env::SimpPriority;

    let mut env = setup_env_with_nat();
    env.init_eq().unwrap();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let one_name = Name::from_string("Nat.one");
    if env.get_const(&one_name).is_none() {
        env.add_decl(Declaration::Axiom {
            name: one_name.clone(),
            level_params: vec![],
            type_: nat.clone(),
        })
        .unwrap();
    }
    let one = Expr::const_(one_name, vec![]);

    // Add Nat.two as a constant
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat.two"),
        level_params: vec![],
        type_: nat.clone(),
    })
    .unwrap();

    let two = Expr::const_(Name::from_string("Nat.two"), vec![]);

    // LHS = Nat.add Nat.one Nat.one
    let lhs = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.add"), vec![]),
            one.clone(),
        ),
        one.clone(),
    );

    // Type: Eq Nat (Nat.add Nat.one Nat.one) Nat.two
    let lemma_type = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat.clone(),
            ),
            lhs.clone(),
        ),
        two.clone(),
    );

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("my_add_lemma"),
        level_params: vec![],
        type_: lemma_type,
    })
    .unwrap();

    // Register it as a simp lemma in the environment registry
    env.register_simp_lemma(Name::from_string("my_add_lemma"), SimpPriority::Default);

    // Goal: Eq Nat (Nat.add Nat.one Nat.one) Nat.two
    let eq_goal = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat,
            ),
            lhs,
        ),
        two,
    );

    let mut state = ProofState::new(env, eq_goal);

    // simp should find my_add_lemma from the registry and close with rfl
    let result = simp_default(&mut state);
    assert!(
        result.is_ok(),
        "simp should succeed using registered env lemma, got: {result:?}"
    );
}

#[test]
fn test_simp_excludes_registered_lemma_when_excluded() {
    use clean_kernel::env::SimpPriority;

    let mut env = setup_env_with_nat();
    env.init_eq().unwrap();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // Register a trivial lemma: trivial_simp : Eq Nat Nat.zero Nat.zero
    let lemma_type = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat,
            ),
            zero.clone(),
        ),
        zero,
    );

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("trivial_simp"),
        level_params: vec![],
        type_: lemma_type,
    })
    .unwrap();

    env.register_simp_lemma(Name::from_string("trivial_simp"), SimpPriority::Default);

    // Verify it's in the registry
    assert!(env.is_simp_lemma(&Name::from_string("trivial_simp")));

    // Collect lemmas with trivial_simp excluded
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let state = ProofState::new(env, target);
    let mut config = SimpConfig::new();
    config.exclude.insert("trivial_simp".to_string());

    let lemmas = collect_simp_lemmas(&state, &config);
    assert!(
        !lemmas
            .iter()
            .any(|l| l.name == Name::from_string("trivial_simp")),
        "excluded lemma should not appear in simp lemma set"
    );
}

#[test]
fn test_collect_simp_lemmas_includes_registry_entries() {
    use clean_kernel::env::SimpPriority;

    let mut env = setup_env_with_nat();
    env.init_eq().unwrap();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // Register a custom lemma
    let lemma_type = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat,
            ),
            zero.clone(),
        ),
        zero,
    );

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("custom_simp_lemma"),
        level_params: vec![],
        type_: lemma_type,
    })
    .unwrap();

    env.register_simp_lemma(
        Name::from_string("custom_simp_lemma"),
        SimpPriority::Custom(500),
    );

    let target = Expr::const_(Name::from_string("A"), vec![]);
    let state = ProofState::new(env, target);
    let config = SimpConfig::new();

    let lemmas = collect_simp_lemmas(&state, &config);

    let found = lemmas
        .iter()
        .find(|l| l.name == Name::from_string("custom_simp_lemma"));
    assert!(found.is_some(), "registry lemma should appear in simp set");
    assert_eq!(
        found.unwrap().priority,
        500,
        "priority should match SimpPriority::Custom(500)"
    );
}

#[test]
fn test_collect_simp_lemmas_registry_order_stable_for_equal_priority() {
    use clean_kernel::env::SimpPriority;

    let mut env = setup_env_with_nat();
    env.init_eq().unwrap();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    let mk_type = || {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                    nat.clone(),
                ),
                zero.clone(),
            ),
            zero.clone(),
        )
    };

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("zzz_simp"),
        level_params: vec![],
        type_: mk_type(),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("aaa_simp"),
        level_params: vec![],
        type_: mk_type(),
    })
    .unwrap();

    // Register in reverse lexical order to ensure collection order is stabilized.
    env.register_simp_lemma(Name::from_string("zzz_simp"), SimpPriority::Default);
    env.register_simp_lemma(Name::from_string("aaa_simp"), SimpPriority::Default);

    let target = Expr::const_(Name::from_string("A"), vec![]);
    let state = ProofState::new(env, target);
    let config = SimpConfig::new();

    let names: Vec<String> = collect_simp_lemmas(&state, &config)
        .into_iter()
        .filter(|lemma| {
            lemma.name == Name::from_string("aaa_simp")
                || lemma.name == Name::from_string("zzz_simp")
        })
        .map(|lemma| lemma.name.to_string())
        .collect();

    assert_eq!(names, vec!["aaa_simp", "zzz_simp"]);
}

/// End-to-end test: simp closes a goal using a registry lemma on custom types.
///
/// Uses `Color` and `paint`/`splash` constants with zero overlap with hardcoded
/// Nat/Bool builtins, proving the registry path is the sole rewrite source.
#[test]
fn test_simp_closes_goal_via_registry_only_custom_types() {
    use clean_kernel::env::SimpPriority;

    let mut env = setup_env();
    env.init_eq().unwrap();

    let color = Expr::const_(Name::from_string("Color"), vec![]);

    // Declare Color : Type
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Color"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    // Declare paint : Color and splash : Color
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("paint"),
        level_params: vec![],
        type_: color.clone(),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("splash"),
        level_params: vec![],
        type_: color.clone(),
    })
    .unwrap();

    let paint = Expr::const_(Name::from_string("paint"), vec![]);
    let splash = Expr::const_(Name::from_string("splash"), vec![]);

    // Declare color_eq : Eq Color paint splash
    let lemma_type = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                color.clone(),
            ),
            paint.clone(),
        ),
        splash.clone(),
    );

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("color_eq"),
        level_params: vec![],
        type_: lemma_type,
    })
    .unwrap();

    // Register color_eq as a simp lemma
    env.register_simp_lemma(Name::from_string("color_eq"), SimpPriority::Custom(200));

    // Goal: Eq Color paint splash
    let goal_expr = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                color,
            ),
            paint,
        ),
        splash,
    );

    let mut state = ProofState::new(env, goal_expr);

    // simp must close this via the registry lemma; no hardcoded lemma can fire
    let result = simp_default(&mut state);
    assert!(
        result.is_ok(),
        "simp should close goal using registry-only custom-type lemma, got: {result:?}"
    );
    assert!(
        state.goals().is_empty(),
        "goal should be closed after simp with registry lemma"
    );
}

// Tests for ring tactic

#[test]
fn test_ring_simple_equality() {
    let mut env = setup_env_with_nat();
    env.init_eq().unwrap();

    // Goal: Nat.zero = Nat.zero
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    let eq = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat,
            ),
            zero.clone(),
        ),
        zero,
    );

    let mut state = ProofState::new(env, eq);

    // ring should close this
    ring(&mut state).expect("ring should close Nat.zero = Nat.zero");
    assert!(state.goals().is_empty());
}

#[test]
fn test_ring_not_equality_fails() {
    let env = setup_env_with_nat();

    // Goal: Nat (not an equality)
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    let mut state = ProofState::new(env, nat);

    let result = ring(&mut state);
    assert!(matches!(result, Err(TacticError::GoalMismatch(_))));
}

#[test]
fn test_ring_normalize_zero() {
    // Test that Nat.zero normalizes to Const(0)
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let norm = ring_normalize(&zero);
    assert_eq!(norm, RingExpr::Const(0));
}

#[test]
fn test_ring_normalize_succ() {
    // Test that Nat.succ Nat.zero normalizes to Const(1)
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let one = Expr::app(succ, zero);

    let norm = ring_normalize(&one);
    assert_eq!(norm, RingExpr::Const(1));
}

#[test]
fn test_ring_flatten_add() {
    // Test a + (b + c) flattens to Add([a, b, c])
    let a = RingExpr::Var("a".to_string());
    let b = RingExpr::Var("b".to_string());
    let c = RingExpr::Var("c".to_string());

    let bc = ring_flatten_add(b.clone(), c.clone());
    let abc = ring_flatten_add(a.clone(), bc);

    // Should be flattened (sorted)
    if let RingExpr::Add(terms) = abc {
        assert_eq!(terms.len(), 3);
    } else {
        panic!("Expected Add");
    }
}

#[test]
fn test_ring_collect_constants() {
    // Test that 1 + 2 + 3 = 6
    let result = ring_flatten_add(
        RingExpr::Const(1),
        ring_flatten_add(RingExpr::Const(2), RingExpr::Const(3)),
    );
    assert_eq!(result, RingExpr::Const(6));
}

#[test]
fn test_ring_mul_by_zero() {
    // Test that a * 0 = 0
    let a = RingExpr::Var("a".to_string());
    let result = ring_flatten_mul(a, RingExpr::Const(0));
    assert_eq!(result, RingExpr::Const(0));
}

#[test]
fn test_ring_mul_by_one() {
    // Test that a * 1 = a
    let a = RingExpr::Var("a".to_string());
    let result = ring_flatten_mul(a.clone(), RingExpr::Const(1));
    assert_eq!(result, a);
}

// Tests for norm_num tactic

#[test]
fn test_norm_num_simple_equality() {
    let mut env = setup_env_with_nat();
    env.init_eq().unwrap();

    // Goal: Nat.zero = Nat.zero
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    let eq = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat,
            ),
            zero.clone(),
        ),
        zero,
    );

    let mut state = ProofState::new(env, eq);

    // norm_num should close this
    norm_num(&mut state).expect("norm_num should close Nat.zero = Nat.zero");
    assert!(state.goals().is_empty());
}

#[test]
fn test_norm_num_evaluate_succ() {
    // Test that Nat.succ (Nat.succ Nat.zero) evaluates to 2
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let one = Expr::app(succ.clone(), zero);
    let two = Expr::app(succ, one);

    let result = eval_nat_expr(&two);
    assert_eq!(result, Some(2));
}

#[test]
fn test_norm_num_eval_nat_zero() {
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    assert_eq!(eval_nat_expr(&zero), Some(0));
}

#[test]
fn test_norm_num_eval_nat_one() {
    let one = Expr::const_(Name::from_string("Nat.one"), vec![]);
    assert_eq!(eval_nat_expr(&one), Some(1));
}

#[test]
fn test_norm_num_unequal_values_fails() {
    let mut env = setup_env_with_nat();
    env.init_eq().unwrap();

    // Goal: Nat.zero = Nat.succ Nat.zero (0 = 1, should fail)
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let one = Expr::app(succ, zero.clone());

    let eq = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat,
            ),
            zero,
        ),
        one,
    );

    let mut state = ProofState::new(env, eq);

    let err = norm_num(&mut state).unwrap_err();
    assert!(
        matches!(
            err,
            TacticError::ArithmeticFailed { .. }
                | TacticError::NoProgress { .. }
                | TacticError::GoalMismatch(_)
        ),
        "norm_num on 0 = 1 should produce error, got: {err}"
    );
}

// Tests for beta/eta reduction helpers

#[test]
fn test_beta_reduce_simple() {
    // (λ x => x) reduces to identity, and (λ x => x) a reduces to a
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);

    let identity = Expr::lam(BinderInfo::Default, a_ty.clone(), Expr::bvar(0));

    let app = Expr::app(identity, a.clone());
    let reduced = beta_reduce(&app);

    assert_eq!(reduced, a);
}

#[test]
fn test_beta_reduce_nested() {
    // (λ x => λ y => x) a b reduces to a
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);

    let inner = Expr::lam(
        BinderInfo::Default,
        a_ty.clone(),
        Expr::bvar(1), // refers to x
    );

    let outer = Expr::lam(BinderInfo::Default, a_ty.clone(), inner);

    let app1 = Expr::app(outer, a.clone());
    let app2 = Expr::app(app1, b);

    let reduced = beta_reduce(&app2);
    assert_eq!(reduced, a);
}

#[test]
fn test_eta_reduce_simple() {
    // λ x => f x reduces to f (when x not free in f)
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    let f = Expr::const_(Name::from_string("f"), vec![]);

    let eta_expandable = Expr::lam(
        BinderInfo::Default,
        a_ty,
        Expr::app(f.clone(), Expr::bvar(0)),
    );

    let reduced = eta_reduce(&eta_expandable);
    assert_eq!(reduced, f);
}

#[test]
fn test_eta_no_reduce_when_var_used() {
    // λ x => x x should NOT eta reduce (x appears in function position)
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);

    let non_eta = Expr::lam(
        BinderInfo::Default,
        a_ty,
        Expr::app(Expr::bvar(0), Expr::bvar(0)),
    );

    let reduced = eta_reduce(&non_eta);
    // Should be unchanged since bvar(0) appears in function position
    assert_eq!(reduced, non_eta);
}

#[test]
fn test_contains_bvar() {
    // Test contains_bvar function
    let e1 = Expr::bvar(0);
    assert!(contains_bvar(&e1, 0));
    assert!(!contains_bvar(&e1, 1));

    let e2 = Expr::const_(Name::from_string("a"), vec![]);
    assert!(!contains_bvar(&e2, 0));

    let e3 = Expr::app(Expr::bvar(0), Expr::bvar(1));
    assert!(contains_bvar(&e3, 0));
    assert!(contains_bvar(&e3, 1));
    assert!(!contains_bvar(&e3, 2));
}

#[test]
fn test_substitute_bvar() {
    // Test substitute_bvar function
    let replacement = Expr::const_(Name::from_string("a"), vec![]);

    // bvar(0) -> a
    let e1 = Expr::bvar(0);
    let result = substitute_bvar(&e1, 0, &replacement);
    assert_eq!(result, replacement);

    // bvar(1) -> bvar(0) (shift down)
    let e2 = Expr::bvar(1);
    let result2 = substitute_bvar(&e2, 0, &replacement);
    assert_eq!(result2, Expr::bvar(0));

    // Nonzero target index is still supported.
    let e3 = Expr::app(Expr::bvar(2), Expr::bvar(1));
    let result3 = substitute_bvar(&e3, 1, &replacement);
    assert_eq!(result3, Expr::app(Expr::bvar(1), replacement));
}

#[test]
fn test_shift_expr() {
    // Test shift_expr function
    let e = Expr::bvar(0);

    // Shift up by 1
    let shifted = shift_expr(&e, 1);
    assert_eq!(shifted, Expr::bvar(1));

    // Shift up by 2
    let shifted2 = shift_expr(&e, 2);
    assert_eq!(shifted2, Expr::bvar(2));

    // Shift down by 1.
    let e2 = Expr::app(Expr::bvar(1), Expr::bvar(2));
    let shifted3 = shift_expr(&e2, -1);
    assert_eq!(shifted3, Expr::app(Expr::bvar(0), Expr::bvar(1)));
}

#[test]
fn test_simp_expr_lam_body_produces_funext_proof() {
    // Exercise the mk_funext path: when simp simplifies a lambda body,
    // the result should have a non-None proof term (funext-based).
    //
    // Input: λ n : Nat, Nat.add n Nat.zero
    // Expected simplified: λ n : Nat, n  (via Nat.add_zero)
    // Expected proof: Some(funext ...) (not None)
    use crate::tactic::simp::{collect_simp_lemmas, simp_expr, SimpConfig};

    let mut env = setup_env_with_nat();
    env.init_eq().unwrap();
    env.init_nat_arith_lemmas().unwrap();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    // Build: λ n : Nat, Nat.add n Nat.zero
    // Body under binder: Nat.add (bvar 0) Nat.zero
    let body = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.add"), vec![]),
            Expr::bvar(0),
        ),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );
    let lam_expr = Expr::lam(BinderInfo::Default, nat.clone(), body);

    // Set up a dummy goal to drive simp_expr
    let target = Expr::const_(Name::from_string("True"), vec![]);
    let state = ProofState::new(env, target);
    let goal = state.current_goal().unwrap().clone();

    let config = SimpConfig::new();
    let lemmas = collect_simp_lemmas(&state, &config);

    let result = simp_expr(&state, &goal, &lam_expr, &lemmas, &config);

    // The body should be simplified: Nat.add n 0 → n (bvar 0)
    let expected = Expr::lam(BinderInfo::Default, nat, Expr::bvar(0));
    assert_eq!(
        result.expr, expected,
        "lambda body should be simplified from (Nat.add n 0) to n"
    );

    // The proof must be Some — mk_funext wraps the body proof in funext
    assert!(
        result.proof.is_some(),
        "simp_expr on lambda body should produce a funext-based proof, got None"
    );
}

#[test]
fn test_simp_expr_pi_body_produces_forall_congr_proof() {
    // mk_forall_congr path: Prop-valued Pi body produces propext(forall_congr(...)) proof.
    // Input: ∀ n : Nat, Nat.add 0 0 = 0. Expected: ∀ n : Nat, 0 = 0.
    use crate::tactic::simp::{collect_simp_lemmas, simp_expr, SimpConfig};
    let mut env = setup_env_with_nat();
    env.init_eq().unwrap();
    env.init_nat_arith_lemmas().unwrap();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // Build body: @Eq Nat (Nat.add Nat.zero Nat.zero) Nat.zero
    // This is Prop-valued (it's an equality of Nats)
    let add_zero_zero = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.add"), vec![]),
            zero.clone(),
        ),
        zero.clone(),
    );
    let body = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat.clone(),
            ),
            add_zero_zero,
        ),
        zero.clone(),
    );

    // Build Pi: ∀ n : Nat, body
    let pi_expr = Expr::pi(BinderInfo::Default, nat.clone(), body);

    // Set up a dummy goal
    let target = Expr::const_(Name::from_string("True"), vec![]);
    let state = ProofState::new(env, target);
    let goal = state.current_goal().unwrap().clone();

    let config = SimpConfig::new();
    let lemmas = collect_simp_lemmas(&state, &config);

    let result = simp_expr(&state, &goal, &pi_expr, &lemmas, &config);

    // The body should be simplified: Nat.add 0 0 → 0
    // Since B102 the `Nat.add_zero` lemma matches the SURFACE form structurally
    // (no eager pre-WHNF), so `?n` binds the surface operand `Nat.zero` and the
    // rewrite yields the named constant — previously the pre-WHNF bound `?n` to
    // the literal-collapsed `Lit(Nat 0)`. Both represent 0 and are def-eq.
    let expected_body = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                nat.clone(),
            ),
            zero.clone(),
        ),
        zero.clone(),
    );
    let expected = Expr::pi(BinderInfo::Default, nat, expected_body);
    assert_eq!(
        result.expr, expected,
        "Pi body should be simplified from (Nat.add 0 0 = 0) to (0 = 0)"
    );

    // Structural proof check (Re: #2115): propext(pi_old, pi_new, forall_congr(α, p, q, h_iff))
    let proof = result
        .proof
        .as_ref()
        .expect("should produce forall_congr proof");
    let head = proof.get_app_fn();
    let args = proof.get_app_args();
    assert!(matches!(head.kind(), ExprKind::Const(n, _) if n.to_string() == "propext"));
    assert_eq!(args.len(), 3, "propext expects 3 args, got {}", args.len());
    let inner_head = args[2].get_app_fn();
    assert!(matches!(inner_head.kind(), ExprKind::Const(n, _) if n.to_string() == "forall_congr"));
    assert_eq!(
        args[2].get_app_args().len(),
        4,
        "forall_congr expects 4 args"
    );
}

// Tests for Proj/MData BVar traversal (#2128)

#[test]
fn test_contains_bvar_proj() {
    // Proj wrapping a BVar should be detected
    let proj_with_bvar = Expr::proj(Name::from_string("Prod.fst"), 0, Expr::bvar(0));
    assert!(contains_bvar(&proj_with_bvar, 0));
    assert!(!contains_bvar(&proj_with_bvar, 1));

    // Nested: Proj wrapping App containing BVar
    let nested = Expr::proj(
        Name::from_string("Prod.snd"),
        1,
        Expr::app(Expr::const_(Name::from_string("f"), vec![]), Expr::bvar(2)),
    );
    assert!(contains_bvar(&nested, 2));
    assert!(!contains_bvar(&nested, 0));
}

#[test]
fn test_contains_bvar_mdata() {
    // MData wrapping a BVar should be detected
    let mdata_with_bvar = Expr::mdata(vec![], Expr::bvar(0));
    assert!(contains_bvar(&mdata_with_bvar, 0));
    assert!(!contains_bvar(&mdata_with_bvar, 1));

    // MData wrapping an App containing BVar
    let nested = Expr::mdata(
        vec![],
        Expr::app(Expr::bvar(1), Expr::const_(Name::from_string("a"), vec![])),
    );
    assert!(contains_bvar(&nested, 1));
    assert!(!contains_bvar(&nested, 0));
}

#[test]
fn test_substitute_bvar_proj() {
    // Substituting inside a Proj should recurse into the struct expression
    let replacement = Expr::const_(Name::from_string("s"), vec![]);
    let proj = Expr::proj(Name::from_string("Prod.fst"), 0, Expr::bvar(0));
    let result = substitute_bvar(&proj, 0, &replacement);

    let expected = Expr::proj(Name::from_string("Prod.fst"), 0, replacement);
    assert_eq!(result, expected);
}

#[test]
fn test_substitute_bvar_mdata() {
    // Substituting inside an MData should recurse into the inner expression
    let replacement = Expr::const_(Name::from_string("a"), vec![]);
    let mdata = Expr::mdata(vec![], Expr::bvar(0));
    let result = substitute_bvar(&mdata, 0, &replacement);

    let expected = Expr::mdata(vec![], replacement);
    assert_eq!(result, expected);
}

#[test]
fn test_shift_expr_proj() {
    // Shifting inside a Proj should recurse into the struct expression
    let proj = Expr::proj(Name::from_string("Prod.fst"), 0, Expr::bvar(0));
    let shifted = shift_expr(&proj, 2);

    let expected = Expr::proj(Name::from_string("Prod.fst"), 0, Expr::bvar(2));
    assert_eq!(shifted, expected);
}

#[test]
fn test_shift_expr_mdata() {
    // Shifting inside an MData should recurse into the inner expression
    let mdata = Expr::mdata(vec![], Expr::bvar(1));
    let shifted = shift_expr(&mdata, 3);

    let expected = Expr::mdata(vec![], Expr::bvar(4));
    assert_eq!(shifted, expected);
}

#[test]
fn test_beta_reduce_proj() {
    // Beta-reducing inside a Proj should recurse
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    // Proj(fst, 0, (λ x => x) a) should reduce to Proj(fst, 0, a)
    let identity = Expr::lam(BinderInfo::Default, a_ty, Expr::bvar(0));
    let proj = Expr::proj(
        Name::from_string("Prod.fst"),
        0,
        Expr::app(identity, a.clone()),
    );
    let reduced = beta_reduce(&proj);

    let expected = Expr::proj(Name::from_string("Prod.fst"), 0, a);
    assert_eq!(reduced, expected);
}

/// Build an environment with propext + Iff and two atomic propositions `P`, `Q`.
///
/// `Iff`/`propext` are required so an `@[simp]` lemma `P ↔ Q` can be turned into
/// an `Eq` rewrite (`P = Q`) by the simp engine.
fn setup_env_with_p_q_iff() -> Environment {
    let mut env = setup_env_with_prop_ext();
    let prop = Expr::prop();
    for name in ["P", "Q"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: prop.clone(),
        })
        .unwrap();
    }
    env
}

/// Lean 4 parity (simp-iff-bidirectional): an `@[simp]` lemma whose conclusion
/// is `Iff a b` must be usable as a left-to-right rewrite `a → b`. Clean
/// previously only extracted `@Eq` conclusions, so an iff simp lemma was dropped
/// and simp made no progress. This pins the fixed behavior end-to-end.
#[test]
fn test_simp_iff_registry_lemma_rewrites_lhs_to_rhs_and_closes() {
    use clean_kernel::env::SimpPriority;

    let mut env = setup_env_with_p_q_iff();
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);

    // my_iff : Iff P Q
    let iff_ty = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Iff"), vec![]), p.clone()),
        q.clone(),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("my_iff"),
        level_params: vec![],
        type_: iff_ty,
    })
    .unwrap();
    env.register_simp_lemma(Name::from_string("my_iff"), SimpPriority::Default);

    // Goal: Q → P. After `intro hq : Q`, simp must rewrite the goal P to Q
    // (via the iff lemma) and close it with `assumption` against hq.
    let goal = Expr::arrow(q, p);
    let mut state = ProofState::new(env, goal);
    intro(&mut state, "hq").unwrap();

    let result = simp_default(&mut state);
    assert!(
        result.is_ok(),
        "simp should rewrite P->Q via iff lemma then close via assumption, got: {result:?}"
    );
    assert!(
        state.goals().is_empty(),
        "goal should be closed after iff rewrite + assumption, {} remain",
        state.goals().len()
    );
}

/// The iff lemma is collected into the simp set with `lhs = P`, `rhs = Q`, and a
/// `proof_expr` carrying the `propext`-based `Eq` witness (not `None`, which
/// would be wrong for a non-`Eq` source lemma).
#[test]
fn test_collect_simp_lemmas_includes_iff_lemma_lhs_rhs() {
    use clean_kernel::env::SimpPriority;

    let mut env = setup_env_with_p_q_iff();
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);

    let iff_ty = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Iff"), vec![]), p.clone()),
        q.clone(),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("pq_iff"),
        level_params: vec![],
        type_: iff_ty,
    })
    .unwrap();
    env.register_simp_lemma(Name::from_string("pq_iff"), SimpPriority::Default);

    let target = Expr::const_(Name::from_string("P"), vec![]);
    let state = ProofState::new(env, target);
    let config = SimpConfig::new();

    let lemmas = collect_simp_lemmas(&state, &config);
    let found = lemmas
        .iter()
        .find(|l| l.name == Name::from_string("pq_iff"))
        .expect("iff lemma should be collected into the simp set");
    assert_eq!(
        found.lhs, p,
        "iff lemma lhs should be the iff's left side P"
    );
    assert_eq!(
        found.rhs, q,
        "iff lemma rhs should be the iff's right side Q"
    );
    assert!(
        found.proof_expr.is_some(),
        "iff lemma must carry a propext-based Eq proof template, not proof_expr=None"
    );
}

/// Negative: a one-directional implication `P → Q` is symmetric in NEITHER
/// direction, so it must NOT be registered as a simp rewrite rule (in
/// particular, simp must not reverse it). Only `Eq`/`Iff` conclusions become
/// rewrites; an arrow has no `Eq`/`Iff` head and is dropped.
#[test]
fn test_collect_simp_lemmas_does_not_register_implication_as_rewrite() {
    use clean_kernel::env::SimpPriority;

    let mut env = setup_env_with_p_q_iff();
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);

    // pq_imp : P → Q  (an implication, NOT an iff or eq).
    let imp_ty = Expr::arrow(p, q);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("pq_imp"),
        level_params: vec![],
        type_: imp_ty,
    })
    .unwrap();
    env.register_simp_lemma(Name::from_string("pq_imp"), SimpPriority::Default);

    let target = Expr::const_(Name::from_string("P"), vec![]);
    let state = ProofState::new(env, target);
    let config = SimpConfig::new();

    let lemmas = collect_simp_lemmas(&state, &config);
    assert!(
        !lemmas.iter().any(|l| l.name == Name::from_string("pq_imp")),
        "a one-directional implication must not become a simp rewrite rule"
    );
}

/// Negative (soundness): the iff rewrite fires only left-to-right. With
/// `my_iff : P ↔ Q`, simp rewrites `P` but must NOT rewrite `Q` back to `P`.
/// A goal that is exactly `Q` (with only `P` provable) stays open.
#[test]
fn test_simp_iff_lemma_not_applied_in_reverse() {
    use clean_kernel::env::SimpPriority;

    let mut env = setup_env_with_p_q_iff();
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);

    let iff_ty = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Iff"), vec![]), p.clone()),
        q.clone(),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("my_iff"),
        level_params: vec![],
        type_: iff_ty,
    })
    .unwrap();
    env.register_simp_lemma(Name::from_string("my_iff"), SimpPriority::Default);

    // Goal: P → Q. After `intro hp : P`, the goal is Q. The lemma rewrites the
    // LHS `P` (here the hypothesis is P, the goal is Q); simp must NOT rewrite
    // the goal Q back to P, so it cannot close via assumption hp : P and the
    // tactic reports NoProgress.
    let goal = Expr::arrow(p, q);
    let mut state = ProofState::new(env, goal);
    intro(&mut state, "hp").unwrap();

    let result = simp_default(&mut state);
    assert!(
        matches!(result, Err(TacticError::NoProgress { .. })),
        "simp must not reverse the iff (rewrite Q->P) to close the goal, got: {result:?}"
    );
    assert!(
        !state.goals().is_empty(),
        "goal Q should remain open since the iff is only left-to-right"
    );
}

/// Under-binders parity: a universally-quantified iff lemma
/// `∀ (n : Nat), R n ↔ S n` rewrites `R Nat.zero` to `S Nat.zero`. This
/// exercises the binder-aware `propext` proof template (binder_count = 1): the
/// lemma is instantiated at the matched argument before being wrapped by
/// propext, so the produced `Eq` proof type-checks.
#[test]
fn test_simp_iff_lemma_under_forall_binder_rewrites_at_argument() {
    use clean_kernel::env::SimpPriority;

    let mut env = setup_env_with_prop_ext();
    env.init_nat().unwrap();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_to_prop = Expr::arrow(nat.clone(), Expr::prop());
    for name in ["R", "S"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: nat_to_prop.clone(),
        })
        .unwrap();
    }

    // param_iff : ∀ (n : Nat), Iff (R n) (S n)
    let iff_body = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Iff"), vec![]),
            Expr::app(Expr::const_(Name::from_string("R"), vec![]), Expr::bvar(0)),
        ),
        Expr::app(Expr::const_(Name::from_string("S"), vec![]), Expr::bvar(0)),
    );
    let iff_ty = Expr::pi(BinderInfo::Default, nat.clone(), iff_body);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("param_iff"),
        level_params: vec![],
        type_: iff_ty,
    })
    .unwrap();
    env.register_simp_lemma(Name::from_string("param_iff"), SimpPriority::Default);

    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let r_zero = Expr::app(Expr::const_(Name::from_string("R"), vec![]), zero.clone());
    let s_zero = Expr::app(Expr::const_(Name::from_string("S"), vec![]), zero);

    // Goal: S Nat.zero → R Nat.zero. After `intro hs : S Nat.zero`, simp should
    // rewrite the goal R Nat.zero to S Nat.zero and close via assumption.
    let goal = Expr::arrow(s_zero, r_zero);
    let mut state = ProofState::new(env, goal);
    intro(&mut state, "hs").unwrap();

    let result = simp_default(&mut state);
    assert!(
        result.is_ok(),
        "simp should rewrite R 0 -> S 0 via universally-quantified iff lemma, got: {result:?}"
    );
    assert!(
        state.goals().is_empty(),
        "goal should be closed after under-binder iff rewrite, {} remain",
        state.goals().len()
    );
}

#[test]
fn test_eta_reduce_proj() {
    // Eta-reducing inside a Proj should recurse
    let f = Expr::const_(Name::from_string("f"), vec![]);
    let a_ty = Expr::const_(Name::from_string("A"), vec![]);
    // Proj(fst, 0, λ x => f x) should reduce to Proj(fst, 0, f)
    let eta_expandable = Expr::lam(
        BinderInfo::Default,
        a_ty,
        Expr::app(f.clone(), Expr::bvar(0)),
    );
    let proj = Expr::proj(Name::from_string("Prod.fst"), 0, eta_expandable);
    let reduced = eta_reduce(&proj);

    let expected = Expr::proj(Name::from_string("Prod.fst"), 0, f);
    assert_eq!(reduced, expected);
}

#[test]
fn test_simp_star_tier_identity_siblings_survive_specific_tree_hit() {
    // B103: the WHNF-rotted identity siblings (Nat.mul_zero / Nat.zero_mul /
    // Nat.sub_zero / Nat.sub_self / Nat.zero_sub / Nat.sub_one /
    // List.append_nil / List.length_nil) must be STAR-TIER (Unindexed):
    // offered as candidates at EVERY query, including one where the
    // discrimination tree returns a specific-but-unrelated hit. With Normal
    // indexing their ι/δ-rotted keys either mint a bogus-specific key or are
    // only reachable through the empty-match full-scan fallback — so any
    // specific tree hit at the queried node silently shadows them (B102's
    // shadowing disease, extended to the siblings).
    use crate::tactic::simp::{collect_simp_lemmas, SimpConfig};

    let env = Environment::with_prelude();
    let target = Expr::const_(Name::from_string("True"), vec![]);
    let state = ProofState::new(env, target);
    let goal = state
        .current_goal()
        .expect("fresh state has a goal")
        .clone();

    let config = SimpConfig::new();
    let lemmas = collect_simp_lemmas(&state, &config);

    // Query with a guaranteed NON-EMPTY, specific tree hit unrelated to the
    // siblings: `And True True` keys at the (non-rotting, inductive-headed)
    // `And` node, hitting and_true / true_and / and_self. A non-empty match
    // bypasses the historical empty-match full-scan fallback, so only
    // genuinely star-keyed lemmas are appended.
    let true_c = Expr::const_(Name::from_string("True"), vec![]);
    let query = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("And"), vec![]),
            true_c.clone(),
        ),
        true_c,
    );
    let names: Vec<String> = lemmas
        .candidates(&state, &goal, &query)
        .iter()
        .map(|lemma| lemma.name.to_string())
        .collect();

    // Sanity: the tree hit itself is present (non-empty match path taken).
    assert!(
        names.iter().any(|n| n == "and_true"),
        "query `And True True` should tree-hit and_true; got candidates: {names:?}"
    );

    for sibling in [
        "Nat.mul_zero",
        "Nat.zero_mul",
        "Nat.sub_zero",
        "Nat.sub_self",
        "Nat.zero_sub",
        "Nat.sub_one",
        "List.append_nil",
        "List.length_nil",
    ] {
        assert!(
            names.iter().any(|n| n == sibling),
            "star-tier identity sibling {sibling} must be offered at a \
             foreign specific tree hit; got candidates: {names:?}"
        );
    }
}
