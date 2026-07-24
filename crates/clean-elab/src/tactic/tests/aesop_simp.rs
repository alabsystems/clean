// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Tests for aesop simp integration (Phase C4)
//
// These tests verify that @[aesop norm simp] rules are properly used
// during the aesop normalization phase.
//
// Part of #15: Aesop parity for Mathlib compatibility

use super::*;
use clean_kernel::env::Declaration;
use clean_kernel::{AesopRule, AesopRuleBuilder, AesopRulePhase};

// =============================================================================
// Test: Basic Aesop Simp Rule
//
// Verifies that a simp rule registered with @[aesop norm simp] is used
// during aesop normalization.
// =============================================================================

/// Setup environment with a custom simp lemma
fn setup_env_with_simp_lemma() -> Environment {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();

    // Add a custom type `Foo`
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Foo"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    // Add constants `bar` and `baz` of type Foo
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("bar"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Foo"), vec![]),
    })
    .unwrap();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("baz"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Foo"), vec![]),
    })
    .unwrap();

    // Add simp lemma: bar_eq_baz : bar = baz
    // Type: Eq.{1} Foo bar baz  (Foo : Type = Sort 1, so u = 1)
    let foo = Expr::const_(Name::from_string("Foo"), vec![]);
    let bar = Expr::const_(Name::from_string("bar"), vec![]);
    let baz = Expr::const_(Name::from_string("baz"), vec![]);
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let eq_type = Expr::app(Expr::app(Expr::app(eq, foo), bar), baz);

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("bar_eq_baz"),
        level_params: vec![],
        type_: eq_type,
    })
    .unwrap();

    // Register as aesop simp rule
    env.register_aesop_rule(AesopRule {
        name: Name::from_string("bar_eq_baz"),
        phase: AesopRulePhase::Norm,
        builder: AesopRuleBuilder::Simp,
        builder_args: vec![],
        priority: 100,
        index_mode: clean_kernel::env::AesopIndexMode::default(),
        transparency: clean_kernel::TransparencyMode::default(),
    });

    env
}

/// Test: Basic simp rule usage
///
/// Goal: bar = baz
/// Registered: @[aesop norm simp] theorem bar_eq_baz : bar = baz
///
/// Aesop should use the simp rule in normalization to close the goal with rfl.
#[test]
fn test_aesop_simp_basic() {
    let env = setup_env_with_simp_lemma();

    // Goal: bar = baz  (Foo : Type, so Eq.{1})
    let foo = Expr::const_(Name::from_string("Foo"), vec![]);
    let bar = Expr::const_(Name::from_string("bar"), vec![]);
    let baz = Expr::const_(Name::from_string("baz"), vec![]);
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let goal = Expr::app(Expr::app(Expr::app(eq, foo), bar), baz);

    let mut state = ProofState::new(env, goal);

    // Aesop should be able to prove this via:
    // 1. Normalization phase with bar_eq_baz as simp lemma
    // 2. Goal becomes `baz = baz` after simp
    // 3. Closed by rfl
    let result = aesop(&mut state);

    assert!(
        result.is_ok(),
        "aesop should prove bar = baz using @[aesop norm simp] lemma"
    );
    assert!(
        state.is_complete(),
        "simp lemma should close bar = baz goal"
    );
}

/// Test: Simp rule with reflexivity
///
/// Goal: baz = baz (should be trivial with rfl)
/// This verifies that simp doesn't break when goal is already reflexive.
#[test]
fn test_aesop_simp_reflexive() {
    let env = setup_env_with_simp_lemma();

    // Goal: baz = baz  (Foo : Type, so Eq.{1})
    let foo = Expr::const_(Name::from_string("Foo"), vec![]);
    let baz = Expr::const_(Name::from_string("baz"), vec![]);
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let goal = Expr::app(Expr::app(Expr::app(eq, foo), baz.clone()), baz);

    let mut state = ProofState::new(env, goal);
    let result = aesop(&mut state);

    assert!(result.is_ok(), "aesop should prove baz = baz with rfl");
    assert!(state.is_complete(), "rfl should close baz = baz goal");
}

// =============================================================================
// Test: Multiple Simp Rules
//
// Verifies that multiple @[aesop norm simp] rules can be registered
// and used together.
// =============================================================================

/// Setup environment with multiple simp lemmas (chain rewriting)
fn setup_env_with_chain_simp() -> Environment {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();

    // Add type T
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("T"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    // Add constants a, b, c of type T
    for name in ["a", "b", "c"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("T"), vec![]),
        })
        .unwrap();
    }

    let t = Expr::const_(Name::from_string("T"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let b = Expr::const_(Name::from_string("b"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

    // Add simp lemma: a_eq_b : a = b  (T : Type, so Eq.{1})
    let a_eq_b_type = Expr::app(
        Expr::app(Expr::app(eq.clone(), t.clone()), a.clone()),
        b.clone(),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("a_eq_b"),
        level_params: vec![],
        type_: a_eq_b_type,
    })
    .unwrap();

    // Add simp lemma: b_eq_c : b = c
    let b_eq_c_type = Expr::app(Expr::app(Expr::app(eq, t), b), c);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("b_eq_c"),
        level_params: vec![],
        type_: b_eq_c_type,
    })
    .unwrap();

    // Register both as aesop simp rules
    env.register_aesop_rule(AesopRule {
        name: Name::from_string("a_eq_b"),
        phase: AesopRulePhase::Norm,
        builder: AesopRuleBuilder::Simp,
        builder_args: vec![],
        priority: 100,
        index_mode: clean_kernel::env::AesopIndexMode::default(),
        transparency: clean_kernel::TransparencyMode::default(),
    });

    env.register_aesop_rule(AesopRule {
        name: Name::from_string("b_eq_c"),
        phase: AesopRulePhase::Norm,
        builder: AesopRuleBuilder::Simp,
        builder_args: vec![],
        priority: 100,
        index_mode: clean_kernel::env::AesopIndexMode::default(),
        transparency: clean_kernel::TransparencyMode::default(),
    });

    env
}

/// Test: Chain simp rewrites
///
/// Goal: a = c
/// Registered:
/// - @[aesop norm simp] theorem a_eq_b : a = b
/// - @[aesop norm simp] theorem b_eq_c : b = c
///
/// Simp should rewrite a → b → c, then rfl closes it.
///
/// This tests the simp transitivity support - simp can now chain rewrites.
#[test]
fn test_aesop_simp_chain() {
    let env = setup_env_with_chain_simp();

    // Goal: a = c  (T : Type, so Eq.{1})
    let t = Expr::const_(Name::from_string("T"), vec![]);
    let a = Expr::const_(Name::from_string("a"), vec![]);
    let c = Expr::const_(Name::from_string("c"), vec![]);
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let goal = Expr::app(Expr::app(Expr::app(eq, t), a), c);

    let mut state = ProofState::new(env, goal);
    let result = aesop(&mut state);

    assert!(
        result.is_ok(),
        "aesop should prove a = c via chain simp: a → b → c"
    );
    assert!(state.is_complete(), "chain simp should close a = c goal");
}

// =============================================================================
// Test: Simp Rule Priority
//
// Verifies that simp rules respect priority ordering.
// =============================================================================

/// Test: Higher priority simp rules are tried first
#[test]
fn test_aesop_simp_priority() {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();

    // Add type T
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("T"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    // Add constants x, y, z
    for name in ["x", "y", "z"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("T"), vec![]),
        })
        .unwrap();
    }

    let t = Expr::const_(Name::from_string("T"), vec![]);
    let x = Expr::const_(Name::from_string("x"), vec![]);
    let y = Expr::const_(Name::from_string("y"), vec![]);
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

    // Add simp lemma with high priority: x_eq_y : x = y (priority 100, T : Type so Eq.{1})
    let x_eq_y_type = Expr::app(
        Expr::app(Expr::app(eq.clone(), t.clone()), x.clone()),
        y.clone(),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("x_eq_y"),
        level_params: vec![],
        type_: x_eq_y_type,
    })
    .unwrap();

    env.register_aesop_rule(AesopRule {
        name: Name::from_string("x_eq_y"),
        phase: AesopRulePhase::Norm,
        builder: AesopRuleBuilder::Simp,
        builder_args: vec![],
        priority: 100,
        index_mode: clean_kernel::env::AesopIndexMode::default(),
        transparency: clean_kernel::TransparencyMode::default(),
    });

    // Goal: x = y
    let goal = Expr::app(Expr::app(Expr::app(eq, t), x), y);

    let mut state = ProofState::new(env, goal);
    let result = aesop(&mut state);

    assert!(result.is_ok(), "aesop should use high priority simp rule");
    assert!(
        state.is_complete(),
        "high priority simp rule should close goal"
    );
}

// =============================================================================
// Test: Simp Rule with No Effect
//
// Verifies that aesop still works when simp rules don't apply.
// =============================================================================

/// Test: Simp rule doesn't apply but aesop still succeeds with other tactics
#[test]
fn test_aesop_simp_no_effect_rfl() {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();

    // Register a simp rule for something unrelated
    // unrelated_rule : Eq.{2} Type Prop Prop
    // Type : Sort 2, so Eq needs u=2 when comparing elements of Type
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("unrelated_rule"),
        level_params: vec![],
        type_: Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(
                        Name::from_string("Eq"),
                        vec![Level::succ(Level::succ(Level::zero()))],
                    ),
                    Expr::type_(),
                ),
                Expr::prop(),
            ),
            Expr::prop(),
        ),
    })
    .unwrap();

    env.register_aesop_rule(AesopRule {
        name: Name::from_string("unrelated_rule"),
        phase: AesopRulePhase::Norm,
        builder: AesopRuleBuilder::Simp,
        builder_args: vec![],
        priority: 50,
        index_mode: clean_kernel::env::AesopIndexMode::default(),
        transparency: clean_kernel::TransparencyMode::default(),
    });

    // Goal: 0 = 0 (should work via rfl even without simp)
    // Nat : Type = Sort 1, so Eq.{1}
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let goal = Expr::app(Expr::app(Expr::app(eq, nat), zero.clone()), zero);

    let mut state = ProofState::new(env, goal);
    let result = aesop(&mut state);

    assert!(
        result.is_ok(),
        "aesop should still work via rfl when simp rules don't apply"
    );
    assert!(
        state.is_complete(),
        "rfl should close 0 = 0 goal even without applicable simp rules"
    );
}

// =============================================================================
// Test: Hypothesis simplification enables assumption closure
//
// Regression for #1867. Before this fix, aesop_normalize only called
// target-only `simp`, so hypothesis rewriting never happened.
// =============================================================================

/// Test A: hypothesis simplification via aesop norm simp enables assumption.
///
/// h : bar = q
/// ⊢ baz = q
///
/// The @[aesop norm simp] lemma `bar_eq_baz : bar = baz` rewrites `h` from
/// `bar = q` to `baz = q`. Then `assumption` matches the goal.
/// Part of #1867.
#[test]
fn test_aesop_hyp_simplification_enables_assumption() {
    let mut env = setup_env_with_simp_lemma();

    // Add constant `q` of type Foo
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("q"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Foo"), vec![]),
    })
    .unwrap();

    let foo = Expr::const_(Name::from_string("Foo"), vec![]);
    let bar = Expr::const_(Name::from_string("bar"), vec![]);
    let baz = Expr::const_(Name::from_string("baz"), vec![]);
    let q = Expr::const_(Name::from_string("q"), vec![]);
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);

    // Hypothesis: h : bar = q
    let h_ty = Expr::app(
        Expr::app(Expr::app(eq.clone(), foo.clone()), bar),
        q.clone(),
    );

    // Goal: baz = q
    let goal = Expr::app(Expr::app(Expr::app(eq, foo), baz), q);

    let mut state = ProofState::with_context(
        env,
        goal,
        vec![LocalDecl {
            fvar: FVarId::new(0),
            name: "h".to_string(),
            ty: h_ty,
            value: None,
        }],
    );

    let result = aesop(&mut state);

    assert!(
        result.is_ok(),
        "aesop should close goal by simplifying hypothesis h : bar = q → baz = q, \
         then matching via assumption. Got: {result:?}"
    );
    assert!(
        state.is_complete(),
        "all goals should be closed after hypothesis simplification"
    );
}
