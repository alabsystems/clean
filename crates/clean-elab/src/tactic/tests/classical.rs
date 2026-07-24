// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for classical logic and connective tactics:
//! split, left, right, exfalso, contradiction, by_contra, existsi, by_cases.
//!
//! Extracted from core.rs during #307 large file split.

use super::*;
use clean_kernel::env::Declaration;

// =========================================================================
// Split / disjunction tactic tests
// =========================================================================

#[test]
fn test_split_and_produces_two_goals() {
    let env = setup_env_with_and_or();

    let p_ty = Expr::const_(Name::from_string("P"), vec![]);
    let q_ty = Expr::const_(Name::from_string("Q"), vec![]);
    let target = Expr::app(
        Expr::app(Expr::const_(Name::from_string("And"), vec![]), p_ty.clone()),
        q_ty.clone(),
    );

    let mut state = ProofState::new(env, target);

    split_(&mut state).unwrap();

    assert_eq!(state.goals().len(), 2, "split should create two subgoals");
    assert_eq!(
        state.goals()[0].target,
        p_ty,
        "first goal should be left conjunct"
    );
    assert_eq!(
        state.goals()[1].target,
        q_ty,
        "second goal should be right conjunct"
    );

    // Solve both subgoals
    exact(&mut state, Expr::const_(Name::from_string("p"), vec![])).unwrap();
    exact(&mut state, Expr::const_(Name::from_string("q"), vec![])).unwrap();

    assert!(
        state.is_complete(),
        "split proof should complete after both conjuncts"
    );

    // Proof term should be And.intro P Q p q
    let mut expected = Expr::const_(Name::from_string("And.intro"), vec![]);
    expected = Expr::app(expected, Expr::const_(Name::from_string("P"), vec![]));
    expected = Expr::app(expected, Expr::const_(Name::from_string("Q"), vec![]));
    expected = Expr::app(expected, Expr::const_(Name::from_string("p"), vec![]));
    expected = Expr::app(expected, Expr::const_(Name::from_string("q"), vec![]));

    assert_eq!(
        state.instantiated_proof().unwrap(),
        expected,
        "split should build And.intro proof"
    );
}

#[test]
fn test_constructor_on_and_reuses_split_proof_shape() {
    let env = setup_env_with_and_or();

    let p_ty = Expr::const_(Name::from_string("P"), vec![]);
    let q_ty = Expr::const_(Name::from_string("Q"), vec![]);
    let target = Expr::app(
        Expr::app(Expr::const_(Name::from_string("And"), vec![]), p_ty.clone()),
        q_ty.clone(),
    );

    let mut state = ProofState::new(env, target);

    constructor(&mut state).unwrap();

    assert_eq!(
        state.goals().len(),
        2,
        "constructor on And should open both conjunct goals"
    );

    exact(&mut state, Expr::const_(Name::from_string("p"), vec![])).unwrap();
    exact(&mut state, Expr::const_(Name::from_string("q"), vec![])).unwrap();

    assert!(
        state.is_complete(),
        "constructor-based conjunction proof should complete"
    );

    let mut expected = Expr::const_(Name::from_string("And.intro"), vec![]);
    expected = Expr::app(expected, Expr::const_(Name::from_string("P"), vec![]));
    expected = Expr::app(expected, Expr::const_(Name::from_string("Q"), vec![]));
    expected = Expr::app(expected, Expr::const_(Name::from_string("p"), vec![]));
    expected = Expr::app(expected, Expr::const_(Name::from_string("q"), vec![]));

    assert_eq!(
        state.instantiated_proof().unwrap(),
        expected,
        "constructor should build the same checked And.intro proof as split"
    );
}

#[test]
fn test_split_goal_mismatch() {
    let env = setup_env_with_and_or();
    let target = Expr::const_(Name::from_string("P"), vec![]);
    let mut state = ProofState::new(env, target);

    let result = split_(&mut state);
    assert!(
        matches!(result, Err(TacticError::GoalMismatch(_))),
        "split on non-conjunction should fail"
    );
}

// =========================================================================
// `constructor` subgoal tagging (`case left`/`case right`/`case mp`/`case mpr`)
//
// Lean 4's `constructor` tags the subgoals with the applied constructor's
// field names (`And.intro` → `left`/`right`, `Iff.intro` → `mp`/`mpr`), so
// `case <tag> =>` can focus them out of order. These tests pin the tag names
// and the order-independent focus-by-tag semantics that `compound_case` uses.
// =========================================================================

/// Locate a goal by exact tag and swap it to the front, mirroring the exact-tag
/// lookup in `compound_case` (`builtins_compound.rs`). Returns whether a goal
/// with that tag was found and focused.
fn focus_by_tag(state: &mut ProofState, tag: &str) -> bool {
    match state
        .goals
        .iter()
        .position(|g| g.tag.as_deref() == Some(tag))
    {
        Some(i) => {
            state.goals.swap(0, i);
            true
        }
        None => false,
    }
}

#[test]
fn test_constructor_on_and_tags_subgoals_left_right() {
    let env = setup_env_with_and_or();
    let p_ty = Expr::const_(Name::from_string("P"), vec![]);
    let q_ty = Expr::const_(Name::from_string("Q"), vec![]);
    let target = Expr::app(
        Expr::app(Expr::const_(Name::from_string("And"), vec![]), p_ty.clone()),
        q_ty.clone(),
    );

    let mut state = ProofState::new(env, target);
    constructor(&mut state).expect("constructor should split And P Q");

    assert_eq!(state.goals().len(), 2, "expected two subgoals");
    assert_eq!(
        state.goals()[0].tag.as_deref(),
        Some("left"),
        "first And subgoal must be tagged `left` (And.intro's first field)"
    );
    assert_eq!(
        state.goals()[1].tag.as_deref(),
        Some("right"),
        "second And subgoal must be tagged `right` (And.intro's second field)"
    );

    // `case left => exact p`, then `case right => exact q` — focus by tag.
    assert!(focus_by_tag(&mut state, "left"), "tag `left` must be found");
    exact(&mut state, Expr::const_(Name::from_string("p"), vec![]))
        .expect("exact p closes the `left` case");
    assert!(
        focus_by_tag(&mut state, "right"),
        "tag `right` must be found"
    );
    exact(&mut state, Expr::const_(Name::from_string("q"), vec![]))
        .expect("exact q closes the `right` case");
    assert!(
        state.is_complete(),
        "constructor + case left/right should complete the proof"
    );
}

#[test]
fn test_constructor_on_and_case_focus_is_order_independent() {
    let env = setup_env_with_and_or();
    let p_ty = Expr::const_(Name::from_string("P"), vec![]);
    let q_ty = Expr::const_(Name::from_string("Q"), vec![]);
    let target = Expr::app(
        Expr::app(Expr::const_(Name::from_string("And"), vec![]), p_ty),
        q_ty,
    );

    let mut state = ProofState::new(env, target);
    constructor(&mut state).expect("constructor should split And P Q");

    // Reversed order: focus `right` before `left`. Must still close.
    assert!(
        focus_by_tag(&mut state, "right"),
        "tag `right` must be found"
    );
    exact(&mut state, Expr::const_(Name::from_string("q"), vec![]))
        .expect("exact q closes the `right` case first");
    assert!(focus_by_tag(&mut state, "left"), "tag `left` must be found");
    exact(&mut state, Expr::const_(Name::from_string("p"), vec![]))
        .expect("exact p closes the `left` case second");
    assert!(
        state.is_complete(),
        "reversed case focus (right before left) should complete the proof"
    );
}

#[test]
fn test_constructor_on_and_rejects_bogus_case_tag() {
    let env = setup_env_with_and_or();
    let p_ty = Expr::const_(Name::from_string("P"), vec![]);
    let q_ty = Expr::const_(Name::from_string("Q"), vec![]);
    let target = Expr::app(
        Expr::app(Expr::const_(Name::from_string("And"), vec![]), p_ty),
        q_ty,
    );

    let mut state = ProofState::new(env, target);
    constructor(&mut state).expect("constructor should split And P Q");

    // No subgoal carries the tag `bogus`: focus must fail closed (the real
    // `case` tactic surfaces `no goal with tag 'bogus'`), never panic.
    assert!(
        !focus_by_tag(&mut state, "bogus"),
        "there is no goal tagged `bogus`; focus must fail, not match a real tag"
    );
    // The legitimate tags remain intact and focusable after the failed lookup.
    assert!(
        focus_by_tag(&mut state, "left"),
        "the real `left` tag survives a failed bogus lookup"
    );
}

#[test]
fn test_constructor_on_iff_tags_subgoals_mp_mpr() {
    // `setup_env_with_prop_ext` initialises `Iff` (with `Iff.intro`). Use a
    // single proposition `P` so the goal `Iff P P` yields `mp`/`mpr` subgoals
    // both of type `P → P`.
    let mut env = setup_env_with_prop_ext();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .expect("add proposition P");

    let p_ty = Expr::const_(Name::from_string("P"), vec![]);
    let target = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Iff"), vec![]), p_ty.clone()),
        p_ty.clone(),
    );

    let mut state = ProofState::new(env, target);
    constructor(&mut state).expect("constructor should split Iff P P");

    assert_eq!(state.goals().len(), 2, "expected two Iff subgoals");
    assert_eq!(
        state.goals()[0].tag.as_deref(),
        Some("mp"),
        "first Iff subgoal must be tagged `mp` (Iff.intro's first field)"
    );
    assert_eq!(
        state.goals()[1].tag.as_deref(),
        Some("mpr"),
        "second Iff subgoal must be tagged `mpr` (Iff.intro's second field)"
    );

    // Both arms are `P → P`, closable by the identity lambda `fun h : P => h`.
    let id_p = Expr::lam(
        clean_kernel::BinderInfo::Default,
        p_ty.clone(),
        Expr::bvar(0),
    );

    // Focus and close `mpr` first, then `mp` (order-independent).
    assert!(focus_by_tag(&mut state, "mpr"), "tag `mpr` must be found");
    exact(&mut state, id_p.clone()).expect("id closes the `mpr` arm (P → P)");
    assert!(focus_by_tag(&mut state, "mp"), "tag `mp` must be found");
    exact(&mut state, id_p).expect("id closes the `mp` arm (P → P)");
    assert!(
        state.is_complete(),
        "constructor + case mp/mpr should complete the Iff proof"
    );
}

#[test]
fn test_left_reduces_to_left_goal() {
    let env = setup_env_with_and_or();

    let target = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Or"), vec![]),
            Expr::const_(Name::from_string("P"), vec![]),
        ),
        Expr::const_(Name::from_string("Q"), vec![]),
    );

    let mut state = ProofState::new(env, target);
    left_(&mut state).unwrap();

    assert_eq!(state.goals().len(), 1, "left should leave one subgoal");
    assert_eq!(
        state.goals()[0].target,
        Expr::const_(Name::from_string("P"), vec![]),
        "left should target the left disjunct"
    );

    exact(&mut state, Expr::const_(Name::from_string("p"), vec![])).unwrap();
    assert!(
        state.is_complete(),
        "left then exact p should finish the proof"
    );

    let mut expected = Expr::const_(Name::from_string("Or.inl"), vec![]);
    expected = Expr::app(expected, Expr::const_(Name::from_string("P"), vec![]));
    expected = Expr::app(expected, Expr::const_(Name::from_string("Q"), vec![]));
    expected = Expr::app(expected, Expr::const_(Name::from_string("p"), vec![]));

    assert_eq!(
        state.instantiated_proof().unwrap(),
        expected,
        "left should build Or.inl proof"
    );
}

#[test]
fn test_right_reduces_to_right_goal() {
    let env = setup_env_with_and_or();

    let target = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Or"), vec![]),
            Expr::const_(Name::from_string("P"), vec![]),
        ),
        Expr::const_(Name::from_string("Q"), vec![]),
    );

    let mut state = ProofState::new(env, target);
    right_(&mut state).unwrap();

    assert_eq!(state.goals().len(), 1, "right should leave one subgoal");
    assert_eq!(
        state.goals()[0].target,
        Expr::const_(Name::from_string("Q"), vec![]),
        "right should target the right disjunct"
    );

    exact(&mut state, Expr::const_(Name::from_string("q"), vec![])).unwrap();
    assert!(
        state.is_complete(),
        "right then exact q should finish the proof"
    );

    let mut expected = Expr::const_(Name::from_string("Or.inr"), vec![]);
    expected = Expr::app(expected, Expr::const_(Name::from_string("P"), vec![]));
    expected = Expr::app(expected, Expr::const_(Name::from_string("Q"), vec![]));
    expected = Expr::app(expected, Expr::const_(Name::from_string("q"), vec![]));

    assert_eq!(
        state.instantiated_proof().unwrap(),
        expected,
        "right should build Or.inr proof"
    );
}

#[test]
fn test_left_goal_mismatch() {
    let env = setup_env_with_and_or();
    let target = Expr::const_(Name::from_string("P"), vec![]);
    let mut state = ProofState::new(env, target);

    let result = left_(&mut state);
    assert!(
        matches!(result, Err(TacticError::GoalMismatch(_))),
        "left on non-disjunction should fail"
    );
}

// =========================================================================
// Tests for exfalso, contradiction, and by_contra tactics
// =========================================================================

fn setup_env_with_false() -> Environment {
    let mut env = Environment::new();
    env.init_true_false().unwrap();
    env.init_classical().unwrap();

    let prop = Expr::prop();

    // Propositions P and Q
    for name in ["P", "Q"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: prop.clone(),
        })
        .unwrap();
    }

    // Proof witnesses
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("p"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("P"), vec![]),
    })
    .unwrap();

    // Not P (a proof of P → False)
    let false_type = Expr::const_(Name::from_string("False"), vec![]);
    let not_p_type = Expr::pi(
        BinderInfo::Default,
        Expr::const_(Name::from_string("P"), vec![]),
        false_type.clone(),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("not_p"),
        level_params: vec![],
        type_: not_p_type,
    })
    .unwrap();

    // A proof of False (for some tests)
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("hfalse"),
        level_params: vec![],
        type_: false_type,
    })
    .unwrap();

    env
}

#[test]
fn test_exfalso_changes_goal_to_false() {
    let env = setup_env_with_false();

    // Goal: P
    let target = Expr::const_(Name::from_string("P"), vec![]);
    let mut state = ProofState::new(env, target);

    // Apply exfalso
    exfalso(&mut state).unwrap();

    // Goal should now be False
    assert_eq!(state.goals().len(), 1, "exfalso should leave one goal");
    let false_type = Expr::const_(Name::from_string("False"), vec![]);
    assert_eq!(
        state.goals()[0].target,
        false_type,
        "exfalso should change goal to False"
    );
}

#[test]
fn test_exfalso_then_exact_proves_goal() {
    let env = setup_env_with_false();

    // Goal: P (with h : False in context)
    let target = Expr::const_(Name::from_string("P"), vec![]);
    let false_type = Expr::const_(Name::from_string("False"), vec![]);
    let mut state = ProofState::with_context(
        env,
        target,
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: false_type.clone(),
            value: None,
        }],
    );

    // Apply exfalso
    exfalso(&mut state).unwrap();

    // Goal should now be False
    assert_eq!(state.goals()[0].target, false_type);

    // Now exact h should work
    exact(&mut state, Expr::fvar(FVarId::new(0))).unwrap();
    assert!(
        state.is_complete(),
        "exfalso + exact h should complete proof"
    );
}

#[test]
fn test_exfalso_no_goals_fails() {
    let env = setup_env_with_false();
    let target = Expr::const_(Name::from_string("P"), vec![]);
    let mut state = ProofState::new(env, target);

    // Clear goals
    state.goals.clear();

    let result = exfalso(&mut state);
    assert!(
        matches!(result, Err(TacticError::NoGoals)),
        "exfalso on empty goals should fail"
    );
}

#[test]
fn test_contradiction_with_false_hyp() {
    let env = setup_env_with_false();

    // Goal: Q with h : False
    let target = Expr::const_(Name::from_string("Q"), vec![]);
    let false_type = Expr::const_(Name::from_string("False"), vec![]);
    let mut state = ProofState::with_context(
        env,
        target,
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: false_type,
            value: None,
        }],
    );

    // contradiction should find h : False and prove the goal
    contradiction(&mut state).unwrap();
    assert!(
        state.is_complete(),
        "contradiction with h : False should complete proof"
    );
}

#[test]
fn test_contradiction_with_p_and_not_p() {
    let env = setup_env_with_false();

    // Goal: Q with h1 : P, h2 : P → False
    let target = Expr::const_(Name::from_string("Q"), vec![]);
    let p_type = Expr::const_(Name::from_string("P"), vec![]);
    let false_type = Expr::const_(Name::from_string("False"), vec![]);
    let not_p_type = Expr::pi(BinderInfo::Default, p_type.clone(), false_type);

    let mut state = ProofState::with_context(
        env,
        target,
        vec![
            LocalDecl {
                fvar: FVarId::new(0),
                name: "h1".to_string(),
                ty: p_type,
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(1),
                name: "h2".to_string(),
                ty: not_p_type,
                value: None,
            },
        ],
    );

    // contradiction should find h1 : P and h2 : ¬P
    contradiction(&mut state).unwrap();
    assert!(
        state.is_complete(),
        "contradiction with P and ¬P should complete proof"
    );
}

#[test]
fn test_contradiction_no_contradiction_fails() {
    let env = setup_env_with_false();

    // Goal: Q with no contradictory hypotheses
    let target = Expr::const_(Name::from_string("Q"), vec![]);
    let p_type = Expr::const_(Name::from_string("P"), vec![]);
    let mut state = ProofState::with_context(
        env,
        target,
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: p_type,
            value: None,
        }],
    );

    let result = contradiction(&mut state);
    assert!(
        result.is_err(),
        "contradiction without contradictory hyps should fail"
    );
}

#[test]
fn test_by_contra_introduces_negation() {
    let env = setup_env_with_false();

    // Goal: P
    let target = Expr::const_(Name::from_string("P"), vec![]);
    let mut state = ProofState::new(env, target.clone());

    // by_contra h
    by_contra(&mut state, "h").unwrap();

    // Goal should be False
    let false_type = Expr::const_(Name::from_string("False"), vec![]);
    assert_eq!(state.goals().len(), 1);
    assert_eq!(state.goals()[0].target, false_type);

    // Local context should have h : P → False
    let goal = &state.goals()[0];
    assert_eq!(goal.local_ctx.len(), 1);
    assert_eq!(goal.local_ctx[0].name, "h");
    let expected_neg = Expr::pi(BinderInfo::Default, target, false_type);
    assert_eq!(goal.local_ctx[0].ty, expected_neg);
}

#[test]
fn test_by_contra_then_contradiction() {
    let env = setup_env_with_false();

    // Goal: P with p : P
    let target = Expr::const_(Name::from_string("P"), vec![]);
    let p_type = Expr::const_(Name::from_string("P"), vec![]);
    let mut state = ProofState::with_context(
        env,
        target,
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "hp".to_string(),
            ty: p_type,
            value: None,
        }],
    );

    // by_contra h introduces h : P → False
    by_contra(&mut state, "h").unwrap();

    // Now we have hp : P and h : P → False, so contradiction should work
    contradiction(&mut state).unwrap();
    assert!(
        state.is_complete(),
        "by_contra + contradiction with witness should complete"
    );
}

#[test]
fn test_by_contra_no_classical_fails() {
    // Create environment without classical
    let mut env = Environment::new();
    env.init_true_false().unwrap();
    // Don't init classical

    let prop = Expr::prop();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: prop,
    })
    .unwrap();

    let target = Expr::const_(Name::from_string("P"), vec![]);
    let mut state = ProofState::new(env, target);

    let result = by_contra(&mut state, "h");
    assert!(result.is_err(), "by_contra without Classical should fail");
}

// =========================================================================
// Tests for existsi and by_cases tactics
// =========================================================================

fn setup_env_with_exists() -> Environment {
    let mut env = Environment::new();
    env.init_exists().unwrap();
    env.init_true_false().unwrap();
    env.init_classical().unwrap(); // provides Or.rec for by_cases

    let prop = Expr::prop();

    // Type A
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    // Term a : A
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("a"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("A"), vec![]),
    })
    .unwrap();

    // Predicate P : A → Prop
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            Expr::const_(Name::from_string("A"), vec![]),
            prop.clone(),
        ),
    })
    .unwrap();

    // Pa : P a
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Pa"),
        level_params: vec![],
        type_: Expr::app(
            Expr::const_(Name::from_string("P"), vec![]),
            Expr::const_(Name::from_string("a"), vec![]),
        ),
    })
    .unwrap();

    // Propositions Q and R for by_cases tests
    for name in ["Q", "R"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: prop.clone(),
        })
        .unwrap();
    }

    // q : Q (proof witness)
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("q"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Q"), vec![]),
    })
    .unwrap();

    env
}

#[test]
fn test_existsi_reduces_goal() {
    let env = setup_env_with_exists();

    // Goal: ∃ x : A, P x
    // A : Type (Sort 1), so Exists universe level = Succ(Zero) = 1
    let a_type = Expr::const_(Name::from_string("A"), vec![]);
    let p_const = Expr::const_(Name::from_string("P"), vec![]);
    // Exists {A} P
    let target = Expr::app(
        Expr::app(
            Expr::const_(
                Name::from_string("Exists"),
                vec![Level::succ(Level::zero())],
            ),
            a_type.clone(),
        ),
        p_const.clone(),
    );

    let mut state = ProofState::new(env, target);

    // existsi a
    let witness = Expr::const_(Name::from_string("a"), vec![]);
    existsi(&mut state, witness.clone()).unwrap();

    // Goal should now be P a
    assert_eq!(state.goals().len(), 1);
    let expected = Expr::app(p_const, witness);
    assert_eq!(state.goals()[0].target, expected);
}

#[test]
fn test_existsi_then_exact() {
    let env = setup_env_with_exists();

    // Goal: ∃ x : A, P x
    // A : Type (Sort 1), so Exists universe level = Succ(Zero) = 1
    let a_type = Expr::const_(Name::from_string("A"), vec![]);
    let p_const = Expr::const_(Name::from_string("P"), vec![]);
    let target = Expr::app(
        Expr::app(
            Expr::const_(
                Name::from_string("Exists"),
                vec![Level::succ(Level::zero())],
            ),
            a_type,
        ),
        p_const,
    );

    let mut state = ProofState::new(env, target);

    // existsi a
    existsi(&mut state, Expr::const_(Name::from_string("a"), vec![])).unwrap();

    // exact Pa
    exact(&mut state, Expr::const_(Name::from_string("Pa"), vec![])).unwrap();

    assert!(state.is_complete(), "existsi + exact should complete proof");
}

#[test]
fn test_existsi_wrong_type_fails() {
    let mut env = setup_env_with_exists();

    // Add a type B different from A
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("B"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("b"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("B"), vec![]),
    })
    .unwrap();

    // Goal: ∃ x : A, P x
    // A : Type (Sort 1), so Exists universe level = Succ(Zero) = 1
    let a_type = Expr::const_(Name::from_string("A"), vec![]);
    let p_const = Expr::const_(Name::from_string("P"), vec![]);
    let target = Expr::app(
        Expr::app(
            Expr::const_(
                Name::from_string("Exists"),
                vec![Level::succ(Level::zero())],
            ),
            a_type,
        ),
        p_const,
    );

    let mut state = ProofState::new(env, target);

    // Try to use b : B as witness (should fail)
    let result = existsi(&mut state, Expr::const_(Name::from_string("b"), vec![]));
    assert!(
        matches!(result, Err(TacticError::TypeMismatch { .. })),
        "existsi with wrong type should fail"
    );
}

#[test]
fn test_existsi_non_exists_goal_fails() {
    let env = setup_env_with_exists();

    // Goal: Q (not existential)
    let target = Expr::const_(Name::from_string("Q"), vec![]);
    let mut state = ProofState::new(env, target);

    let result = existsi(&mut state, Expr::const_(Name::from_string("a"), vec![]));
    assert!(
        matches!(result, Err(TacticError::GoalMismatch(_))),
        "existsi on non-existential goal should fail"
    );
}

#[test]
fn test_by_cases_creates_two_goals() {
    let env = setup_env_with_exists();

    // Goal: R
    let target = Expr::const_(Name::from_string("R"), vec![]);
    let mut state = ProofState::new(env, target.clone());

    // by_cases h : Q
    let prop = Expr::const_(Name::from_string("Q"), vec![]);
    by_cases(&mut state, "h", prop.clone()).unwrap();

    // Should have two goals
    assert_eq!(state.goals().len(), 2);

    // Both goals should target R
    assert_eq!(state.goals()[0].target, target);
    assert_eq!(state.goals()[1].target, target);

    // First goal should have h : Q
    assert_eq!(state.goals()[0].local_ctx.len(), 1);
    assert_eq!(state.goals()[0].local_ctx[0].name, "h");
    assert_eq!(state.goals()[0].local_ctx[0].ty, prop);

    // Second goal should have h : ¬Q (Q → False)
    assert_eq!(state.goals()[1].local_ctx.len(), 1);
    assert_eq!(state.goals()[1].local_ctx[0].name, "h");
    let false_type = Expr::const_(Name::from_string("False"), vec![]);
    let neg_q = Expr::pi(BinderInfo::Default, prop, false_type);
    assert_eq!(state.goals()[1].local_ctx[0].ty, neg_q);
}

#[test]
fn test_by_cases_then_assumption() {
    let env = setup_env_with_exists();

    // Goal: Q with q : Q in context
    let target = Expr::const_(Name::from_string("Q"), vec![]);
    let mut state = ProofState::with_context(
        env,
        target,
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "hq".to_string(),
            ty: Expr::const_(Name::from_string("Q"), vec![]),
            value: None,
        }],
    );

    // by_cases h : Q
    by_cases(
        &mut state,
        "h",
        Expr::const_(Name::from_string("Q"), vec![]),
    )
    .unwrap();

    // In positive case (h : Q), we can use h directly
    // Note: The positive hypothesis is added with a new fvar
    let pos_ctx = &state.goals()[0].local_ctx;
    let h_fvar = pos_ctx.iter().find(|d| d.name == "h").unwrap().fvar;
    exact(&mut state, Expr::fvar(h_fvar)).unwrap();

    // In negative case, we still have hq : Q from original context
    // (The hypothesis is fvar 0)
    exact(&mut state, Expr::fvar(FVarId::new(0))).unwrap();

    assert!(
        state.is_complete(),
        "by_cases + assumption should complete proof"
    );
}

#[test]
fn test_by_cases_no_classical_fails() {
    let mut env = Environment::new();
    env.init_true_false().unwrap();
    // Don't init classical

    let prop = Expr::prop();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Q"),
        level_params: vec![],
        type_: prop.clone(),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("R"),
        level_params: vec![],
        type_: prop,
    })
    .unwrap();

    let target = Expr::const_(Name::from_string("R"), vec![]);
    let mut state = ProofState::new(env, target);

    let result = by_cases(
        &mut state,
        "h",
        Expr::const_(Name::from_string("Q"), vec![]),
    );
    assert!(result.is_err(), "by_cases without Classical should fail");
}
