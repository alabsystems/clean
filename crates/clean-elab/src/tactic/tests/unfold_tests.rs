// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Dedicated tests for the unfold, delta, and change tactics.
//!
//! Covers the core definitional unfolding and type-replacement tactics
//! defined in `tactic/unfold.rs` and `tactic/term_close/mod.rs`.
//!
//! Part of #3082.

use super::*;
use clean_kernel::env::Declaration;

// =============================================================================
// Helpers
// =============================================================================

/// Environment with a base type `T`, constants `c : T`, a definition
/// `mydef := c`, and a second definition `mydef2 := c` for multi-unfold tests.
fn setup_unfold_test_env() -> Environment {
    let mut env = Environment::new();
    env.init_eq().unwrap();

    let t = Expr::type_();

    // T : Type
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("T"),
        level_params: vec![],
        type_: t,
    })
    .unwrap();

    let t_const = Expr::const_(Name::from_string("T"), vec![]);

    // c : T
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("c"),
        level_params: vec![],
        type_: t_const.clone(),
    })
    .unwrap();

    // mydef : T := c
    env.add_decl(Declaration::Definition {
        name: Name::from_string("mydef"),
        level_params: vec![],
        type_: t_const.clone(),
        value: Expr::const_(Name::from_string("c"), vec![]),
        is_reducible: true,
    })
    .unwrap();

    // mydef2 : T := c
    env.add_decl(Declaration::Definition {
        name: Name::from_string("mydef2"),
        level_params: vec![],
        type_: t_const.clone(),
        value: Expr::const_(Name::from_string("c"), vec![]),
        is_reducible: true,
    })
    .unwrap();

    // P : T -> Prop (predicate for hypothesis tests)
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, t_const, Expr::prop()),
    })
    .unwrap();

    env
}

// =============================================================================
// Unfold Tests
// =============================================================================

/// unfold replaces a definition in the goal with its body.
#[test]
fn test_unfold_constant_in_goal() {
    let env = setup_unfold_test_env();

    // Goal: P(mydef), i.e. P applied to mydef
    let mydef = Expr::const_(Name::from_string("mydef"), vec![]);
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let target = Expr::app(p.clone(), mydef);

    let mut state = ProofState::new(env, target);
    unfold(&mut state, "mydef").expect("unfold mydef should succeed");

    // After unfold, goal should be P(c)
    let goal = state.current_goal().unwrap();
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let expected = Expr::app(p, c);
    assert_eq!(goal.target, expected, "unfold should replace mydef with c");
}

/// unfold_at replaces a definition in a specific hypothesis.
#[test]
fn test_unfold_at_hypothesis() {
    let env = setup_unfold_test_env();

    let mydef = Expr::const_(Name::from_string("mydef"), vec![]);
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let h_ty = Expr::app(p.clone(), mydef);

    // Goal: some arbitrary target (T)
    let target = Expr::const_(Name::from_string("T"), vec![]);

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

    unfold_at(&mut state, "mydef", "h").expect("unfold_at should succeed");

    let goal = state.current_goal().unwrap();
    // Goal target should be unchanged
    assert_eq!(
        goal.target, target,
        "goal should be unchanged after unfold_at"
    );

    // Hypothesis h should now have P(c) instead of P(mydef)
    let h = goal.local_ctx.iter().find(|d| d.name == "h").unwrap();
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let expected_ty = Expr::app(p, c);
    assert_eq!(
        h.ty, expected_ty,
        "unfold_at should expand mydef to c in hypothesis h"
    );
}

/// Unfolding multiple definitions sequentially.
#[test]
fn test_unfold_multiple() {
    let env = setup_unfold_test_env();

    // Goal: Eq T mydef mydef2
    let mydef = Expr::const_(Name::from_string("mydef"), vec![]);
    let mydef2 = Expr::const_(Name::from_string("mydef2"), vec![]);
    let t_const = Expr::const_(Name::from_string("T"), vec![]);
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let target = Expr::app(Expr::app(Expr::app(eq, t_const), mydef), mydef2);

    let mut state = ProofState::new(env, target);

    // Unfold mydef first
    unfold(&mut state, "mydef").expect("unfold mydef should succeed");
    // Then unfold mydef2
    unfold(&mut state, "mydef2").expect("unfold mydef2 should succeed");

    // After both unfolds, goal should contain c = c (both replaced)
    let goal = state.current_goal().unwrap();
    let _c = Expr::const_(Name::from_string("c"), vec![]);
    // Check that neither mydef nor mydef2 appear in the target
    let consts = collect_consts(&goal.target);
    let has_mydef = consts.iter().any(|n| n.to_string() == "mydef");
    let has_mydef2 = consts.iter().any(|n| n.to_string() == "mydef2");
    assert!(!has_mydef, "mydef should be fully unfolded");
    assert!(!has_mydef2, "mydef2 should be fully unfolded");

    // Both should have been replaced with c
    let has_c = consts.iter().any(|n| n.to_string() == "c");
    assert!(has_c, "c should appear in the unfolded goal");
}

/// unfold fails on a nonexistent constant.
#[test]
fn test_unfold_nonexistent_fails() {
    let env = setup_unfold_test_env();
    let target = Expr::const_(Name::from_string("T"), vec![]);
    let mut state = ProofState::new(env, target);

    let result = unfold(&mut state, "nonexistent_def");
    assert!(
        matches!(result, Err(TacticError::UnfoldFailed { ref name, .. }) if name == "nonexistent_def"),
        "unfold should fail on nonexistent constant: {result:?}"
    );
}

/// delta reduces all definitions without beta-reducing.
///
/// We verify that delta unfolds definition constants but leaves lambda
/// applications unreduced (i.e., it performs delta-reduction only).
#[test]
fn test_delta_no_beta() {
    let mut env = Environment::new();

    // T : Type
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("T"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    let t_const = Expr::const_(Name::from_string("T"), vec![]);

    // c : T
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("c"),
        level_params: vec![],
        type_: t_const.clone(),
    })
    .unwrap();

    // id_def : T -> T := fun (x : T) => x
    let id_body = Expr::lam(BinderInfo::Default, t_const.clone(), Expr::bvar(0));
    env.add_decl(Declaration::Definition {
        name: Name::from_string("id_def"),
        level_params: vec![],
        type_: Expr::arrow(t_const.clone(), t_const.clone()),
        value: id_body.clone(),
        is_reducible: true,
    })
    .unwrap();

    // Goal: id_def c  (application of the definition to c)
    let id_def = Expr::const_(Name::from_string("id_def"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let target = Expr::app(id_def, c.clone());

    let mut state = ProofState::new(env, target);

    // delta unfolds id_def to (fun x => x) but does NOT beta-reduce to c
    delta(&mut state).expect("delta should succeed");

    let goal = state.current_goal().unwrap();
    // The result should be (fun x : T => x) c — the definition is unfolded
    // but the lambda application is not beta-reduced
    let expected = Expr::app(id_body, c);
    assert_eq!(
        goal.target, expected,
        "delta should unfold id_def to its body without beta-reducing"
    );
}

// =============================================================================
// Change Tests
// =============================================================================

/// change succeeds when the new type is definitionally equal.
#[test]
fn test_change_defeq_succeeds() {
    let mut env = Environment::new();

    // T : Type
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("T"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    let t_const = Expr::const_(Name::from_string("T"), vec![]);

    // mydef : T → T := fun x => x
    let id_body = Expr::lam(BinderInfo::Default, t_const.clone(), Expr::bvar(0));
    env.add_decl(Declaration::Definition {
        name: Name::from_string("mydef"),
        level_params: vec![],
        type_: Expr::arrow(t_const.clone(), t_const.clone()),
        value: id_body,
        is_reducible: true,
    })
    .unwrap();

    // c : T
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("c"),
        level_params: vec![],
        type_: t_const.clone(),
    })
    .unwrap();

    // Goal: mydef(c)  which is definitionally equal to c
    let mydef = Expr::const_(Name::from_string("mydef"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let target = Expr::app(mydef, c.clone());

    let mut state = ProofState::new(env, target);

    // change c — should succeed because mydef(c) is def-eq to c via delta+beta
    change(&mut state, c.clone()).expect("change to def-eq type should succeed");

    let goal = state.current_goal().unwrap();
    assert_eq!(goal.target, c, "goal should now be c");
}

/// change fails when the new type is NOT definitionally equal.
#[test]
fn test_change_non_defeq_fails() {
    let mut env = Environment::new();

    // T : Type
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("T"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    let t_const = Expr::const_(Name::from_string("T"), vec![]);

    // c : T
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("c"),
        level_params: vec![],
        type_: t_const.clone(),
    })
    .unwrap();

    // d : T
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("d"),
        level_params: vec![],
        type_: t_const,
    })
    .unwrap();

    // Goal: c
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let d = Expr::const_(Name::from_string("d"), vec![]);

    let mut state = ProofState::new(env, c);

    // change d — should fail because c and d are distinct axioms
    let result = change(&mut state, d);
    assert!(
        matches!(result, Err(TacticError::GoalMismatch(_))),
        "change to non-def-eq type should fail: {result:?}"
    );
}

// =============================================================================
// UnfoldTarget Enum Tests
// =============================================================================

/// UnfoldTarget::Goal and UnfoldTarget::Hypothesis have correct values.
#[test]
fn test_unfold_target_enum() {
    use super::super::unfold::UnfoldTarget;

    let goal_target = UnfoldTarget::Goal;
    let hyp_target = UnfoldTarget::Hypothesis("h".to_string());

    assert_eq!(goal_target, UnfoldTarget::Goal);
    assert_eq!(hyp_target, UnfoldTarget::Hypothesis("h".to_string()));
    assert_ne!(goal_target, hyp_target);

    // Clone works
    let cloned = hyp_target.clone();
    assert_eq!(cloned, hyp_target);

    // Debug format is implemented
    let debug_str = format!("{goal_target:?}");
    assert!(debug_str.contains("Goal"), "Debug should show Goal variant");

    let debug_hyp = format!("{hyp_target:?}");
    assert!(
        debug_hyp.contains("Hypothesis"),
        "Debug should show Hypothesis variant"
    );
}
