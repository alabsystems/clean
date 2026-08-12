// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Focused tests for the `mono` tactic and its helper utilities.

use super::*;

fn add_axioms(env: &mut Environment, ty: &Expr, names: &[&str]) {
    for name in names {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: ty.clone(),
        })
        .unwrap();
    }
}

fn const_expr(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn binary_app(head: &str, lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(Expr::app(const_expr(head), lhs), rhs)
}

#[test]
fn test_mono_config_default() {
    let config = MonoConfig::default();
    assert_eq!(config.max_depth, 10);
    assert!(config.use_all_hyps);
    assert!(config.use_mono_lemmas);
}

#[test]
fn test_mono_config_new() {
    let config = MonoConfig::new();
    assert_eq!(config.max_depth, 10);
}

#[test]
fn test_mono_no_goals() {
    let env = setup_env();
    let target = const_expr("A");
    let mut state = ProofState::new(env, target);
    state.goals.clear();

    let err = mono(&mut state).unwrap_err();
    assert!(
        matches!(err, TacticError::NoGoals),
        "mono on empty goals should produce NoGoals, got: {err:?}"
    );
}

#[test]
fn test_mono_not_relation() {
    let env = setup_env();
    let target = const_expr("A");
    let mut state = ProofState::new(env, target);

    let err = mono(&mut state).unwrap_err();
    assert!(
        matches!(err, TacticError::InvalidTarget { .. }),
        "mono on non-relation goal should produce InvalidTarget error, got: {err:?}"
    );
}

#[test]
fn test_exprs_equal_same_const() {
    let a = const_expr("A");
    let b = const_expr("A");
    assert!(exprs_equal(&a, &b));
}

#[test]
fn test_exprs_equal_different_const() {
    let a = const_expr("A");
    let b = const_expr("B");
    assert!(!exprs_equal(&a, &b));
}

#[test]
fn test_exprs_equal_bvar() {
    let a = Expr::bvar(0);
    let b = Expr::bvar(0);
    let c = Expr::bvar(1);
    assert!(exprs_equal(&a, &b));
    assert!(!exprs_equal(&a, &c));
}

#[test]
fn test_exprs_equal_app() {
    let app1 = Expr::app(const_expr("F"), const_expr("A"));
    let app2 = Expr::app(const_expr("F"), const_expr("A"));
    assert!(exprs_equal(&app1, &app2));
}

#[test]
fn test_make_relation_le() {
    let env = setup_env();
    let a = const_expr("a");
    let b = const_expr("b");
    let nat_ty = const_expr("Nat");
    let nat_inst = const_expr("instLENat");
    let mut state = ProofState::new(env, Expr::sort(Level::zero()));
    let rel = make_relation("le", &nat_ty, &nat_inst, &a, &b, &mut state);

    let args = rel.get_app_args();
    let head = rel.get_app_fn();
    if let ExprKind::Const(name, _) = head.kind() {
        assert_eq!(name.to_string(), "LE.le");
    }
    assert!(args.len() >= 2);
    assert!(exprs_equal(args[args.len() - 1], &b));
}

#[test]
fn test_is_binary_app_true() {
    let app = binary_app("HAdd.hAdd", const_expr("a"), const_expr("b"));
    assert!(is_binary_app(&app, "HAdd.hAdd"));
}

#[test]
fn test_is_binary_app_false() {
    let app = binary_app("F", const_expr("a"), const_expr("b"));
    assert!(!is_binary_app(&app, "HAdd.hAdd"));
}

#[test]
fn test_extract_binary_args() {
    let app = binary_app("F", const_expr("a"), const_expr("b"));
    let (left, right) = extract_binary_args(&app)
        .expect("extracting binary args from App(App(F, a), b) should succeed");
    assert!(exprs_equal(&left, &const_expr("a")));
    assert!(exprs_equal(&right, &const_expr("b")));
}

#[test]
fn test_mono_addition_closes_main_goal_with_checked_nat_proof() {
    let mut env = Environment::with_prelude();
    let nat_ty = const_expr("Nat");
    add_axioms(&mut env, &nat_ty, &["a", "b", "c", "d"]);

    let a = const_expr("a");
    let b = const_expr("b");
    let c = const_expr("c");
    let d = const_expr("d");
    let target = make_nat_le_tc(
        binary_app("Nat.add", a.clone(), b.clone()),
        binary_app("Nat.add", c.clone(), d.clone()),
    );
    let h1_ty = make_nat_le_tc(a.clone(), c.clone());
    let h2_ty = make_nat_le_tc(b.clone(), d.clone());

    let mut state = ProofState::with_context(
        env.clone(),
        target.clone(),
        vec![
            LocalDecl {
                fvar: FVarId::new(0),
                name: "h1".into(),
                ty: h1_ty.clone(),
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(1),
                name: "h2".into(),
                ty: h2_ty.clone(),
                value: None,
            },
        ],
    );

    // RC-N: `gcongr` — which `mono` delegates to for Nat addition — now
    // discharges its own trivial subgoals, so `h1 : a ≤ c` and `h2 : b ≤ d`
    // close the two congruence premises during the decomposition itself. What
    // used to be "decompose, then two manual `assumption` calls" is therefore a
    // single step that leaves NO goals. The subgoal SHAPE is still pinned, by
    // the hypothesis-free sibling test below (and by
    // `gcongr_discharge_tests::test_gcongr_leaves_undischargeable_subgoal_open`),
    // where nothing in context can discharge them and both stay observable.
    mono(&mut state).expect("mono should decompose Nat addition goals");
    assert!(
        state.is_complete(),
        "mono should decompose AND discharge both Nat subgoals from h1/h2, leaving none; got {:?}",
        state.goals
    );
}

#[test]
fn test_mono_addition_subgoal_shape_without_dischargeable_hypotheses() {
    // Same decomposition as above with an EMPTY context: neither congruence
    // premise is dischargeable, so both subgoals survive and their shape can be
    // checked. This is the half of the old
    // `test_mono_addition_closes_main_goal_with_checked_nat_proof` that the
    // RC-N discharger would otherwise make unobservable.
    let mut env = Environment::with_prelude();
    let nat_ty = const_expr("Nat");
    add_axioms(&mut env, &nat_ty, &["a", "b", "c", "d"]);

    let a = const_expr("a");
    let b = const_expr("b");
    let c = const_expr("c");
    let d = const_expr("d");
    let target = make_nat_le_tc(
        binary_app("Nat.add", a.clone(), b.clone()),
        binary_app("Nat.add", c.clone(), d.clone()),
    );
    let mut state = ProofState::new(env, target);

    mono(&mut state).expect("mono should decompose Nat addition goals");
    assert_eq!(state.goals.len(), 2, "mono should create two Nat subgoals");

    let (rel1, _, _, lhs1, rhs1) =
        match_inequality(&state.goals[0].target).expect("first subgoal should stay an inequality");
    let (rel2, _, _, lhs2, rhs2) =
        match_inequality(&state.goals[1].target).expect("second subgoal should stay an inequality");
    assert_eq!(rel1, IneqRel::Le);
    assert_eq!(rel2, IneqRel::Le);
    assert!(exprs_equal(&lhs1, &a));
    assert!(exprs_equal(&rhs1, &c));
    assert!(exprs_equal(&lhs2, &b));
    assert!(exprs_equal(&rhs2, &d));
}

#[test]
fn test_mono_monotone_hypothesis_fails_honestly_without_checked_application() {
    let mut env = Environment::with_prelude();
    let nat_ty = const_expr("Nat");

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("f"),
        level_params: vec![],
        type_: Expr::arrow(nat_ty.clone(), nat_ty.clone()),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Monotone"),
        level_params: vec![],
        type_: Expr::arrow(Expr::arrow(nat_ty.clone(), nat_ty.clone()), Expr::prop()),
    })
    .unwrap();
    add_axioms(&mut env, &nat_ty, &["a", "b"]);

    let mut state = ProofState::with_context(
        env,
        make_nat_le_tc(const_expr("a"), const_expr("b")),
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "hmono".into(),
            ty: Expr::app(const_expr("Monotone"), const_expr("f")),
            value: None,
        }],
    );

    let err = mono(&mut state).unwrap_err();
    assert!(matches!(err, TacticError::SearchExhausted { .. }));
}

#[test]
fn test_mono_addition_non_nat_returns_search_exhausted() {
    let mut env = Environment::with_prelude();
    let int_ty = const_expr("Int");
    add_axioms(&mut env, &int_ty, &["a", "b", "c", "d"]);

    let lhs_add = binary_app("Int.add", const_expr("a"), const_expr("b"));
    let rhs_add = binary_app("Int.add", const_expr("c"), const_expr("d"));

    let mut target_builder = ProofState::new(env.clone(), Expr::prop());
    let target = make_ineq_goal(
        IneqRel::Le,
        &int_ty,
        &const_expr("instLEInt"),
        &lhs_add,
        &rhs_add,
        &mut target_builder,
    );

    let mut state = ProofState::new(env, target);
    let err = mono(&mut state).unwrap_err();
    assert!(matches!(err, TacticError::SearchExhausted { .. }));
}
