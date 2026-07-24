// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Instance and miscellaneous tactic tests (helpers): abs_cases, set_option,
//! trace, positivity_at, clear_all_unused, rename_all, helper functions.

use super::support::make_local;
use super::*;

// ========================================================================
// Tests for abs_cases (N=483)
// ========================================================================

#[test]
fn test_abs_cases_no_goals() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);
    state.goals.clear();

    let result = abs_cases(&mut state, "x");
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_abs_cases_var_not_found() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    let err = abs_cases(&mut state, "nonexistent").unwrap_err();
    assert!(
        matches!(err, TacticError::HypothesisNotFound(ref s) if s == "nonexistent"),
        "abs_cases with missing var should produce HypothesisNotFound('nonexistent'), got: {err}"
    );
}

#[test]
fn test_abs_cases_non_numeric_type() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("B"), vec![]);
    let ctx = vec![LocalDecl {
        fvar: FVarId::new(0),
        name: "x".to_string(),
        ty: Expr::const_(Name::from_string("A"), vec![]), // Non-numeric
        value: None,
    }];
    let mut state = ProofState::with_context(env, target, ctx);

    let result = abs_cases(&mut state, "x");
    assert!(matches!(result, Err(TacticError::InvalidTarget { .. })));
}

#[test]
fn test_abs_cases_with_int() {
    // Part of #2154: abs_cases now uses checked close_goal, which needs the kernel
    // to type-check the Or.rec proof. Requires classical logic + Int ordering + GE.ge.
    // B must be Prop since Or.rec can only eliminate into Prop (0 universe params).
    let env = setup_env_with_int_ord();
    let target = Expr::const_(Name::from_string("B"), vec![]);
    let ctx = vec![LocalDecl {
        fvar: FVarId::new(0),
        name: "x".to_string(),
        ty: Expr::const_(Name::from_string("Int"), vec![]),
        value: None,
    }];
    let mut state = ProofState::with_context(env, target, ctx);

    abs_cases(&mut state, "x").expect("abs_cases should succeed on Int variable");
    // Should create two goals
    assert_eq!(state.goals.len(), 2);
}

/// B103 end-to-end: after the binder-scope fix (one SHARED fvar for the two
/// PARALLEL branch binders, mirroring `by_cases`), closing both branch goals
/// must yield a fully-instantiated Or.rec proof that passes type inference
/// against the original target — not just a scope-check-passing skeleton.
#[test]
fn test_abs_cases_closed_branches_proof_infers_target() {
    use clean_kernel::env::Declaration;

    let mut env = setup_env_with_int_ord();
    // b_wit : B — a witness to close both branch goals with.
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("b_wit"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("B"), vec![]),
    })
    .expect("b_wit axiom registers");

    let target = Expr::const_(Name::from_string("B"), vec![]);
    let ctx = vec![LocalDecl {
        fvar: FVarId::new(0),
        name: "x".to_string(),
        ty: Expr::const_(Name::from_string("Int"), vec![]),
        value: None,
    }];
    let mut state = ProofState::with_context(env, target.clone(), ctx.clone());
    let original_meta = state.current_goal().expect("goal present").meta_id;

    abs_cases(&mut state, "x").expect("abs_cases should succeed on Int variable");
    assert_eq!(state.goals.len(), 2);

    // Close both branch goals with the B witness.
    let b_wit = Expr::const_(Name::from_string("b_wit"), vec![]);
    for case in ["nonneg", "neg"] {
        let goal = state.current_goal().expect("branch goal present").clone();
        state
            .close_goal(&goal, b_wit.clone())
            .unwrap_or_else(|e| panic!("{case} branch should close with b_wit : B: {e}"));
    }
    assert!(state.is_complete(), "both branches closed");

    // The fully-instantiated root proof must infer to B.
    let meta = state.metas.get(original_meta).expect("root meta exists");
    let proof = meta.assignment.clone().expect("root meta assigned");
    let proof = state.metas.instantiate(&proof);
    let goal_view = Goal {
        meta_id: original_meta,
        target: target.clone(),
        local_ctx: ctx,
        tag: None,
    };
    let inferred = state
        .infer_type(&goal_view, &proof)
        .expect("instantiated abs_cases proof should type-infer");
    assert!(
        state.is_def_eq(&goal_view, &inferred, &target),
        "abs_cases closed proof should prove B, inferred: {inferred:?}"
    );
}

/// B103 NEGATIVE (soundness): a branch goal must still reject a wrong
/// witness — `x : Int` does not prove the Prop target `B`.
#[test]
fn test_abs_cases_branch_rejects_wrong_witness() {
    let env = setup_env_with_int_ord();
    let target = Expr::const_(Name::from_string("B"), vec![]);
    let ctx = vec![LocalDecl {
        fvar: FVarId::new(0),
        name: "x".to_string(),
        ty: Expr::const_(Name::from_string("Int"), vec![]),
        value: None,
    }];
    let mut state = ProofState::with_context(env, target, ctx);

    abs_cases(&mut state, "x").expect("abs_cases should succeed on Int variable");
    let goal = state.current_goal().expect("branch goal present").clone();

    // x : Int is not a proof of B.
    let wrong = Expr::fvar(FVarId::new(0));
    let result = state.close_goal(&goal, wrong);
    assert!(
        result.is_err(),
        "branch goal must reject x : Int as a proof of B, got: {result:?}"
    );
    assert_eq!(state.goals.len(), 2, "goals unchanged after rejected close");
}

#[test]
fn test_abs_cases_config() {
    let config = AbsCasesConfig::with_names("pos", "neg");
    assert_eq!(config.nonneg_name, "pos");
    assert_eq!(config.neg_name, "neg");
}

#[test]
fn test_abs_cases_config_default() {
    let config = AbsCasesConfig::new();
    assert_eq!(config.nonneg_name, "h_nonneg");
    assert_eq!(config.neg_name, "h_neg");
}

// ========================================================================
// Tests for set_option (N=483)
// ========================================================================

#[test]
fn test_set_option_valid() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    set_option(&mut state, "verbose", OptionValue::Bool(true))
        .expect("set_option('verbose', true) should succeed");
    // set_option should not modify goals
    assert_eq!(state.goals().len(), 1, "set_option should preserve goals");
}

#[test]
fn test_set_option_invalid() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    let result = set_option(&mut state, "unknown_option", OptionValue::Bool(true));
    assert!(matches!(result, Err(TacticError::InvalidTarget { .. })));
}

#[test]
fn test_set_options_multiple() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    let config = SetOptionConfig::new()
        .set_bool("verbose", true)
        .set_nat("max_depth", 50);
    set_options(&mut state, config).expect("set_options with verbose+max_depth should succeed");
    // set_options should not modify goals
    assert_eq!(state.goals().len(), 1, "set_options should preserve goals");
}

#[test]
fn test_set_option_config_builder() {
    let config = SetOptionConfig::new()
        .set_bool("verbose", true)
        .set_nat("max_depth", 100)
        .set_string("trace", "all");
    assert_eq!(config.options.len(), 3);
}

#[test]
fn test_proof_options_default() {
    let opts = ProofOptions::default();
    assert!(!opts.is_verbose());
    assert_eq!(opts.verbose_override(), None);
    assert!(!opts.is_trace());
    assert_eq!(opts.max_depth(), 100);
    assert_eq!(opts.max_depth_override(), None);
    assert_eq!(opts.timeout_ms(), 0);
    assert!(!opts.is_profile());
}

#[test]
fn test_set_option_stores_verbose() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);
    assert!(
        !state.options().is_verbose(),
        "default verbose should be false"
    );

    set_option(&mut state, "verbose", OptionValue::Bool(true)).unwrap();
    assert!(
        state.options().is_verbose(),
        "verbose should be true after set_option"
    );
    assert_eq!(
        state.options().verbose_override(),
        Some(true),
        "verbose override should preserve the explicit setting"
    );

    set_option(&mut state, "verbose", OptionValue::Bool(false)).unwrap();
    assert!(
        !state.options().is_verbose(),
        "verbose should be false after reset"
    );
    assert_eq!(
        state.options().verbose_override(),
        Some(false),
        "verbose override should track the explicit reset"
    );
}

#[test]
fn test_set_option_stores_max_depth() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);
    assert_eq!(state.options().max_depth(), 100, "default max_depth");

    set_option(&mut state, "max_depth", OptionValue::Nat(500)).unwrap();
    assert_eq!(
        state.options().max_depth(),
        500,
        "max_depth should be updated"
    );
    assert_eq!(
        state.options().max_depth_override(),
        Some(500),
        "max_depth override should preserve the explicit setting"
    );
}

#[test]
fn test_set_option_max_depth_controls_tauto() {
    let mut env = setup_env();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("add P");

    let prop = Expr::const_(Name::from_string("P"), vec![]);
    let mut goal = prop.clone();
    for _ in 0..20 {
        goal = Expr::pi(BinderInfo::Default, prop.clone(), goal);
    }

    let mut default_state = ProofState::new(env.clone(), goal.clone());
    let default_err = tauto(&mut default_state)
        .expect_err("default tauto depth should be exhausted on a 20-step implication chain");
    assert!(
        matches!(default_err, TacticError::NoProgress { .. }),
        "expected depth-limited tauto failure, got {default_err:?}"
    );

    let mut configured_state = ProofState::new(env, goal);
    set_option(&mut configured_state, "max_depth", OptionValue::Nat(21))
        .expect("set_option max_depth should succeed");
    tauto(&mut configured_state)
        .expect("raised max_depth should let tauto finish the implication chain");
    assert!(
        configured_state.is_complete(),
        "tauto should close the goal after the depth override"
    );
}

#[test]
fn test_set_option_max_depth_bounds_tauto_solve_by_elim_fallback() {
    let mut env = setup_env();
    for name in ["DepthA", "DepthB", "DepthC"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .expect("add propositional symbol");
    }

    let prop_a = Expr::const_(Name::from_string("DepthA"), vec![]);
    let prop_b = Expr::const_(Name::from_string("DepthB"), vec![]);
    let prop_c = Expr::const_(Name::from_string("DepthC"), vec![]);
    let ctx = vec![
        make_local(100, "ha", prop_a.clone()),
        make_local(
            101,
            "hab",
            Expr::pi(BinderInfo::Default, prop_a.clone(), prop_b.clone()),
        ),
        make_local(
            102,
            "hbc",
            Expr::pi(BinderInfo::Default, prop_b.clone(), prop_c.clone()),
        ),
    ];

    let mut shallow_state = ProofState::with_context(env.clone(), prop_c.clone(), ctx.clone());
    set_option(&mut shallow_state, "max_depth", OptionValue::Nat(1))
        .expect("set_option max_depth should succeed");
    let shallow_err = tauto(&mut shallow_state)
        .expect_err("max_depth 1 should block the two-step hypothesis-chain fallback");
    assert!(
        matches!(shallow_err, TacticError::NoProgress { .. }),
        "expected depth-limited tauto failure, got {shallow_err:?}"
    );

    let mut configured_state = ProofState::with_context(env, prop_c, ctx);
    set_option(&mut configured_state, "max_depth", OptionValue::Nat(2))
        .expect("set_option max_depth should succeed");
    tauto(&mut configured_state)
        .expect("max_depth 2 should allow the two-step hypothesis-chain fallback");
    assert!(
        configured_state.is_complete(),
        "tauto should close the chained hypothesis goal once the depth budget is high enough"
    );
}

#[test]
fn test_set_option_stores_timeout_ms() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);
    assert_eq!(state.options().timeout_ms(), 0, "default timeout_ms");

    set_option(&mut state, "timeout_ms", OptionValue::Nat(5000)).unwrap();
    assert_eq!(
        state.options().timeout_ms(),
        5000,
        "timeout_ms should be 5000"
    );
}

#[test]
fn test_set_option_type_mismatch_rejects() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    let result = set_option(&mut state, "verbose", OptionValue::Nat(1));
    assert!(result.is_err(), "Bool option with Nat value should fail");

    let result = set_option(&mut state, "max_depth", OptionValue::Bool(true));
    assert!(result.is_err(), "Nat option with Bool value should fail");
}

#[test]
fn test_set_options_stores_multiple() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    let config = SetOptionConfig::new()
        .set_bool("verbose", true)
        .set_nat("max_depth", 50)
        .set_bool("trace", true)
        .set_nat("timeout_ms", 3000);
    set_options(&mut state, config).unwrap();

    assert!(state.options().is_verbose());
    assert_eq!(state.options().max_depth(), 50);
    assert!(state.options().is_trace());
    assert_eq!(state.options().timeout_ms(), 3000);
}

// ========================================================================
// Tests for trace (N=483)
// ========================================================================

#[test]
fn test_trace_basic() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let state = ProofState::new(env, target);

    let output = trace(&state, "test message").expect("trace should succeed");
    assert_eq!(output.message, "test message");
    assert_eq!(output.num_goals, 1);
}

#[test]
fn test_trace_no_goals() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);
    state.goals.clear();

    let output = trace(&state, "test").expect("trace with no goals should succeed");
    assert_eq!(output.goal_summary, "no goals");
    assert_eq!(output.num_goals, 0);
}

#[test]
fn test_trace_with_level() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let state = ProofState::new(env, target);

    let output = trace_with_level(&state, "debug msg", TraceLevel::Debug)
        .expect("trace_with_level should succeed");
    assert_eq!(output.level, TraceLevel::Debug);
}

#[test]
fn test_trace_state() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let state = ProofState::new(env, target);

    let output = trace_state(&state).expect("trace_state should succeed");
    assert!(output.message.contains("Goals: 1"));
}

#[test]
fn test_trace_expr() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let state = ProofState::new(env, target);

    let expr = Expr::const_(Name::from_string("test"), vec![]);
    let output = trace_expr(&state, &expr).expect("trace_expr should succeed");
    assert!(output.message.contains("Expression structure"));
}

#[test]
fn test_trace_level_default() {
    let level = TraceLevel::default();
    assert_eq!(level, TraceLevel::Info);
}

// ========================================================================
// Tests for positivity_at (N=483)
// ========================================================================

#[test]
fn test_positivity_at_no_goals() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);
    state.goals.clear();

    let result = positivity_at(&mut state, "h");
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_positivity_at_hyp_not_found() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    let result = positivity_at(&mut state, "nonexistent");
    assert!(matches!(result, Err(TacticError::HypothesisNotFound(ref s)) if s == "nonexistent"));
}

#[test]
fn test_positivity_at_config() {
    let config = PositivityAtConfig::new().with_name("h_positive");
    assert_eq!(config.result_name, Some("h_positive".to_string()));
    assert!(config.try_stronger);
}

#[test]
fn test_positivity_at_config_default() {
    let config = PositivityAtConfig::new();
    assert_eq!(config.result_name, None);
    assert!(config.try_stronger);
}

// ========================================================================
// Tests for clear_all_unused (N=483)
// ========================================================================

#[test]
fn test_clear_all_unused_no_goals() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);
    state.goals.clear();

    let result = clear_all_unused(&mut state);
    assert!(matches!(result, Err(TacticError::NoGoals)));
}

#[test]
fn test_clear_all_unused_keeps_used() {
    let env = setup_env();
    // Target uses x
    let target = Expr::fvar(FVarId::new(0));
    let ctx = vec![
        LocalDecl {
            fvar: FVarId::new(0),
            name: "x".to_string(),
            ty: Expr::const_(Name::from_string("A"), vec![]),
            value: None,
        },
        LocalDecl {
            fvar: FVarId::new(1),
            name: "y".to_string(),
            ty: Expr::const_(Name::from_string("A"), vec![]),
            value: None,
        },
    ];
    let mut state = ProofState::with_context(env, target, ctx);

    clear_all_unused(&mut state).unwrap();

    let goal = state.current_goal().unwrap();
    // x should remain (used in target), y should be removed
    assert!(goal.local_ctx.iter().any(|d| d.name == "x"));
    assert!(!goal.local_ctx.iter().any(|d| d.name == "y"));
}

#[test]
fn test_clear_all_unused_keeps_dependencies() {
    let env = setup_env();
    // Target uses x, and x depends on y in its type
    let target = Expr::fvar(FVarId::new(0));
    let ctx = vec![
        LocalDecl {
            fvar: FVarId::new(1),
            name: "y".to_string(),
            ty: Expr::const_(Name::from_string("A"), vec![]),
            value: None,
        },
        LocalDecl {
            fvar: FVarId::new(0),
            name: "x".to_string(),
            ty: Expr::fvar(FVarId::new(1)), // x's type depends on y
            value: None,
        },
    ];
    let mut state = ProofState::with_context(env, target, ctx);

    clear_all_unused(&mut state).unwrap();

    let goal = state.current_goal().unwrap();
    // Both x and y should remain
    assert!(goal.local_ctx.iter().any(|d| d.name == "x"));
    assert!(goal.local_ctx.iter().any(|d| d.name == "y"));
}

// ========================================================================
// Tests for rename_all (N=483)
// ========================================================================

#[test]
fn test_rename_all_basic() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let ctx = vec![
        LocalDecl {
            fvar: FVarId::new(0),
            name: "h1".to_string(),
            ty: Expr::const_(Name::from_string("A"), vec![]),
            value: None,
        },
        LocalDecl {
            fvar: FVarId::new(1),
            name: "h2".to_string(),
            ty: Expr::const_(Name::from_string("A"), vec![]),
            value: None,
        },
    ];
    let mut state = ProofState::with_context(env, target, ctx);

    rename_all(&mut state, vec![("h1", "hA"), ("h2", "hB")]).unwrap();

    let goal = state.current_goal().unwrap();
    assert!(goal.local_ctx.iter().any(|d| d.name == "hA"));
    assert!(goal.local_ctx.iter().any(|d| d.name == "hB"));
    assert!(!goal.local_ctx.iter().any(|d| d.name == "h1"));
    assert!(!goal.local_ctx.iter().any(|d| d.name == "h2"));
}

#[test]
fn test_rename_all_not_found() {
    let env = setup_env();
    let target = Expr::const_(Name::from_string("A"), vec![]);
    let mut state = ProofState::new(env, target);

    let result = rename_all(&mut state, vec![("nonexistent", "new_name")]);
    assert!(matches!(result, Err(TacticError::HypothesisNotFound(ref s)) if s == "nonexistent"));
}

// ========================================================================
// Helper function tests (N=483)
// ========================================================================

#[test]
fn test_is_numeric_type_int() {
    assert!(is_numeric_type(&Expr::const_(
        Name::from_string("Int"),
        vec![]
    )));
}

#[test]
fn test_is_numeric_type_real() {
    assert!(is_numeric_type(&Expr::const_(
        Name::from_string("Real"),
        vec![]
    )));
}

#[test]
fn test_is_numeric_type_rat() {
    assert!(is_numeric_type(&Expr::const_(
        Name::from_string("Rat"),
        vec![]
    )));
}

#[test]
fn test_is_numeric_type_non_numeric() {
    assert!(!is_numeric_type(&Expr::const_(
        Name::from_string("Nat"),
        vec![]
    )));
    assert!(!is_numeric_type(&Expr::const_(
        Name::from_string("Bool"),
        vec![]
    )));
}

#[test]
fn test_collect_fvars_basic() {
    let expr = Expr::app(Expr::fvar(FVarId::new(0)), Expr::fvar(FVarId::new(1)));
    let fvars = collect_fvars(&expr);
    assert_eq!(fvars.len(), 2);
    assert!(fvars.contains(&FVarId::new(0)));
    assert!(fvars.contains(&FVarId::new(1)));
}

#[test]
fn test_collect_fvars_no_duplicates() {
    let expr = Expr::app(Expr::fvar(FVarId::new(0)), Expr::fvar(FVarId::new(0)));
    let fvars = collect_fvars(&expr);
    assert_eq!(fvars.len(), 1);
}

#[test]
fn test_collect_fvars_nested() {
    let expr = Expr::lam(
        BinderInfo::Default,
        Expr::fvar(FVarId::new(0)),
        Expr::fvar(FVarId::new(1)),
    );
    let fvars = collect_fvars(&expr);
    assert_eq!(fvars.len(), 2);
}
