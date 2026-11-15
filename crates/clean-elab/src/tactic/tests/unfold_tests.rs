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
    unfold(
        &mut state,
        &clean_parser::SurfaceName::generated_path("mydef"),
    )
    .expect("unfold mydef should succeed");

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
            binder_info: Default::default(),
            fvar: FVarId::new(0),
            name: clean_parser::SurfaceName::generated_path("h"),
            ty: h_ty,
            value: None,
        }],
    );

    unfold_at(
        &mut state,
        &clean_parser::SurfaceName::generated_path("mydef"),
        &clean_parser::SurfaceName::generated_path("h"),
    )
    .expect("unfold_at should succeed");

    let goal = state.current_goal().unwrap();
    // Goal target should be unchanged
    assert_eq!(
        goal.target, target,
        "goal should be unchanged after unfold_at"
    );

    // Hypothesis h should now have P(c) instead of P(mydef)
    let h = goal
        .local_ctx
        .iter()
        .find(|d| d.name == clean_parser::SurfaceName::generated_path("h"))
        .unwrap();
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
    unfold(
        &mut state,
        &clean_parser::SurfaceName::generated_path("mydef"),
    )
    .expect("unfold mydef should succeed");
    // Then unfold mydef2
    unfold(
        &mut state,
        &clean_parser::SurfaceName::generated_path("mydef2"),
    )
    .expect("unfold mydef2 should succeed");

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

    let result = unfold(
        &mut state,
        &clean_parser::SurfaceName::generated_path("nonexistent_def"),
    );
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
    let hyp_target = UnfoldTarget::Hypothesis(clean_parser::SurfaceName::generated_path("h"));

    assert_eq!(goal_target, UnfoldTarget::Goal);
    assert_eq!(
        hyp_target,
        UnfoldTarget::Hypothesis(clean_parser::SurfaceName::generated_path("h"))
    );
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

// =============================================================================
// Head-beta contraction on unfold (Lean `deltaExpand` parity, 2026-09-13)
// =============================================================================

/// Environment for the contraction tests: `T`, `c : T`, `f : T → T`,
/// `P : T → Prop`, and three definitions with binders:
/// - `id_def : T → T := fun x => x`
/// - `k2 : T → T → T := fun x y => x`
/// - `app_def : (T → T) → T → T := fun g => g`
fn setup_beta_env() -> Environment {
    let mut env = setup_unfold_test_env();
    let t = Expr::const_(Name::from_string("T"), vec![]);
    let t_to_t = Expr::arrow(t.clone(), t.clone());

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("f"),
        level_params: vec![],
        type_: t_to_t.clone(),
    })
    .unwrap();
    env.add_decl(Declaration::Definition {
        name: Name::from_string("id_def"),
        level_params: vec![],
        type_: t_to_t.clone(),
        value: Expr::lam(BinderInfo::Default, t.clone(), Expr::bvar(0)),
        is_reducible: true,
    })
    .unwrap();
    env.add_decl(Declaration::Definition {
        name: Name::from_string("k2"),
        level_params: vec![],
        type_: Expr::arrow(t.clone(), t_to_t.clone()),
        value: Expr::lam(
            BinderInfo::Default,
            t.clone(),
            Expr::lam(BinderInfo::Default, t.clone(), Expr::bvar(1)),
        ),
        is_reducible: true,
    })
    .unwrap();
    env.add_decl(Declaration::Definition {
        name: Name::from_string("app_def"),
        level_params: vec![],
        type_: Expr::arrow(t_to_t.clone(), t_to_t),
        value: Expr::lam(
            BinderInfo::Default,
            Expr::arrow(t.clone(), t),
            Expr::bvar(0),
        ),
        is_reducible: true,
    })
    .unwrap();
    env
}

fn k(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

/// `unfold` on an APPLIED definition contracts the value against the
/// occurrence's arguments — Lean's `deltaExpand` (`f.betaRev args`) — so
/// `P (id_def c)` becomes `P c`, not `P ((fun x => x) c)`.
///
/// This is the `unfold` half of the `unfold min2; split` defect (Trust battery
/// row r11): the un-contracted redex was what `split`'s finder walked into.
#[test]
fn test_unfold_applied_definition_head_beta_contracts() {
    let env = setup_beta_env();
    let target = Expr::app(k("P"), Expr::app(k("id_def"), k("c")));
    let mut state = ProofState::new(env, target);

    unfold(
        &mut state,
        &clean_parser::SurfaceName::generated_path("id_def"),
    )
    .expect("unfold id_def should succeed");

    let goal = state.current_goal().unwrap();
    assert_eq!(
        goal.target,
        Expr::app(k("P"), k("c")),
        "unfold must contract `(fun x => x) c` to `c`"
    );
}

/// Two binders, two arguments: `P (k2 c (f c))` → `P c`. The de Bruijn
/// indices are instantiated outermost-first, so the FIRST argument wins.
#[test]
fn test_unfold_two_binders_two_arguments() {
    let env = setup_beta_env();
    let target = Expr::app(
        k("P"),
        Expr::apps(k("k2"), [k("c"), Expr::app(k("f"), k("c"))]),
    );
    let mut state = ProofState::new(env, target);

    unfold(&mut state, &clean_parser::SurfaceName::generated_path("k2"))
        .expect("unfold k2 should succeed");

    assert_eq!(
        state.current_goal().unwrap().target,
        Expr::app(k("P"), k("c")),
        "`k2 c (f c)` must contract to its first argument"
    );
}

/// A PARTIAL application keeps the un-met binder as a lambda:
/// `k2 c` → `fun y => c` (the body no longer mentions `y`).
#[test]
fn test_unfold_partial_application_keeps_remaining_binder() {
    let env = setup_beta_env();
    let t = k("T");
    // Goal: `(k2 c) = (k2 c)` at type `T → T`.
    let lhs = Expr::app(k("k2"), k("c"));
    let target = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [Expr::arrow(t.clone(), t.clone()), lhs.clone(), lhs],
    );
    let mut state = ProofState::new(env, target);

    unfold(&mut state, &clean_parser::SurfaceName::generated_path("k2"))
        .expect("unfold k2 should succeed");

    let expected_side = Expr::lam(BinderInfo::Default, t.clone(), k("c"));
    let expected = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [
            Expr::arrow(t.clone(), t),
            expected_side.clone(),
            expected_side,
        ],
    );
    assert_eq!(
        state.current_goal().unwrap().target,
        expected,
        "a partial application must leave the un-met binder as a lambda"
    );
}

/// SURPLUS arguments stay applied after the binders are consumed:
/// `app_def f c` → `f c`.
#[test]
fn test_unfold_surplus_arguments_stay_applied() {
    let env = setup_beta_env();
    let target = Expr::app(k("P"), Expr::apps(k("app_def"), [k("f"), k("c")]));
    let mut state = ProofState::new(env, target);

    unfold(
        &mut state,
        &clean_parser::SurfaceName::generated_path("app_def"),
    )
    .expect("unfold app_def should succeed");

    assert_eq!(
        state.current_goal().unwrap().target,
        Expr::app(k("P"), Expr::app(k("f"), k("c"))),
        "the surplus argument `c` must stay applied to the contracted head `f`"
    );
}

/// Only the redex CREATED by the unfolding is contracted: a beta-redex the
/// user wrote elsewhere in the goal is untouched, as in Lean.
#[test]
fn test_unfold_leaves_unrelated_user_redex_alone() {
    let env = setup_beta_env();
    let t = k("T");
    let user_redex = Expr::app(
        Expr::lam(BinderInfo::Default, t.clone(), Expr::bvar(0)),
        k("c"),
    );
    let eq = |l: Expr, r: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [t.clone(), l, r],
        )
    };
    let target = eq(k("mydef"), user_redex.clone());
    let mut state = ProofState::new(env, target);

    unfold(
        &mut state,
        &clean_parser::SurfaceName::generated_path("mydef"),
    )
    .expect("unfold mydef should succeed");

    assert_eq!(
        state.current_goal().unwrap().target,
        eq(k("c"), user_redex),
        "unfold must not contract a redex it did not create"
    );
}

/// An occurrence UNDER a binder whose argument is that binder's variable:
/// `∀ x : T, P (id_def x)` → `∀ x : T, P x`. The loose `BVar(0)` argument is
/// substituted with the correct index (no capture, no off-by-one).
#[test]
fn test_unfold_under_binder_instantiates_bound_argument() {
    let env = setup_beta_env();
    let t = k("T");
    let target = Expr::pi(
        BinderInfo::Default,
        t.clone(),
        Expr::app(k("P"), Expr::app(k("id_def"), Expr::bvar(0))),
    );
    let mut state = ProofState::new(env, target);

    unfold(
        &mut state,
        &clean_parser::SurfaceName::generated_path("id_def"),
    )
    .expect("unfold id_def under a binder should succeed");

    assert_eq!(
        state.current_goal().unwrap().target,
        Expr::pi(BinderInfo::Default, t, Expr::app(k("P"), Expr::bvar(0))),
        "the bound argument must be re-indexed correctly after contraction"
    );
}

/// `unfold … at h` contracts too (same helper on the hypothesis type).
#[test]
fn test_unfold_at_applied_definition_head_beta_contracts() {
    let env = setup_beta_env();
    let h_ty = Expr::app(k("P"), Expr::app(k("id_def"), k("c")));
    let mut state = ProofState::with_context(
        env,
        k("T"),
        vec![LocalDecl {
            binder_info: Default::default(),
            fvar: FVarId::new(0),
            name: clean_parser::SurfaceName::generated_path("h"),
            ty: h_ty,
            value: None,
        }],
    );

    unfold_at(
        &mut state,
        &clean_parser::SurfaceName::generated_path("id_def"),
        &clean_parser::SurfaceName::generated_path("h"),
    )
    .expect("unfold_at should succeed");

    let goal = state.current_goal().unwrap();
    let h = goal
        .local_ctx
        .iter()
        .find(|d| d.name == clean_parser::SurfaceName::generated_path("h"))
        .unwrap();
    assert_eq!(
        h.ty,
        Expr::app(k("P"), k("c")),
        "unfold_at must contract the redex in the hypothesis"
    );
}
