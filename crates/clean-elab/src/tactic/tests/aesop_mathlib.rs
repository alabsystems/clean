// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

// Mathlib-style integration tests for aesop
//
// These tests are modeled after common proof patterns in Mathlib4 that
// rely on aesop for automation. They verify that clean's aesop can handle
// the same patterns.
//
// Part of #15: Aesop parity for Mathlib compatibility

use super::*;
use clean_kernel::env::Declaration;

// =============================================================================
// Mathlib Pattern: Logical Equivalence
//
// Many Mathlib proofs use aesop to prove logical equivalences like:
// (A ∧ B) ↔ (B ∧ A) (commutativity)
// =============================================================================

/// Test: And commutativity (Mathlib.Logic.Basic)
///
/// theorem and_comm : P ∧ Q ↔ Q ∧ P := by aesop
///
/// This test verifies that aesop can prove bi-implications via:
/// 1. Split Iff into two implications (P ∧ Q → Q ∧ P and Q ∧ P → P ∧ Q)
/// 2. For each, intro the hypothesis, destruct the And, rebuild swapped
#[test]
fn test_mathlib_and_comm() {
    let env = setup_mathlib_logic_env();

    let p = Expr::const_(Name::from_string("P"), vec![]);
    let q = Expr::const_(Name::from_string("Q"), vec![]);
    let and = Expr::const_(Name::from_string("And"), vec![]);
    let iff = Expr::const_(Name::from_string("Iff"), vec![]);

    // Goal: (P ∧ Q) ↔ (Q ∧ P)
    let p_and_q = Expr::app(Expr::app(and.clone(), p.clone()), q.clone());
    let q_and_p = Expr::app(Expr::app(and, q), p);
    let goal = Expr::app(Expr::app(iff, p_and_q), q_and_p);

    let mut state = ProofState::new(env, goal);

    let result = aesop(&mut state);

    assert!(
        result.is_ok(),
        "aesop should prove and_comm via intro + split + And.intro"
    );
    assert!(state.is_complete(), "and_comm proof should close all goals");
}

/// Setup environment for Mathlib logic tests
fn setup_mathlib_logic_env() -> Environment {
    let mut env = Environment::new();
    env.init_and().unwrap();
    env.init_classical().unwrap();
    env.init_iff().unwrap(); // Initialize Iff with Iff.intro, Iff.mp, Iff.mpr

    let prop = Expr::prop();

    // Add propositions
    for name in ["P", "Q", "R", "S"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: prop.clone(),
        })
        .unwrap();
    }

    env
}

// =============================================================================
// Mathlib Pattern: Simple Existence
//
// aesop handles existential proofs via `use` tactic
// =============================================================================

/// Test: Prove exists by providing witness
///
/// example : ∃ x : Nat, x = 0 := by aesop
///
/// This requires:
/// - Exists inductive type with Exists.intro
/// - Aesop trying common witnesses (like Nat.zero)
/// - rfl to prove 0 = 0
///
/// This test verifies:
/// 1. Existential introduction via `use`
/// 2. Witness enumeration finds `Nat.zero` as a candidate
/// 3. Equality reflexivity via `rfl` closes the subgoal
#[test]
fn test_mathlib_exists_witness() {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_and().unwrap();
    env.init_eq().unwrap(); // Need Eq for equality goals
    env.init_exists().unwrap(); // Need Exists.intro

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]); // Eq.{1} for Nat : Type 0
    let exists_ = Expr::const_(
        Name::from_string("Exists"),
        vec![Level::succ(Level::zero())],
    ); // At Type universe

    // Goal: ∃ x : Nat, x = 0
    // = Exists Nat (λ x => x = 0)
    let body = Expr::app(
        Expr::app(Expr::app(eq, nat.clone()), Expr::bvar(0)),
        zero.clone(),
    );
    let pred = Expr::lam(BinderInfo::Default, nat.clone(), body);
    let goal = Expr::app(Expr::app(exists_, nat), pred);

    let mut state = ProofState::new(env, goal);

    let result = aesop(&mut state);

    assert!(
        result.is_ok(),
        "aesop should prove ∃ x, x = 0 by using 0 and rfl"
    );
    assert!(
        state.is_complete(),
        "exists witness proof should close all goals"
    );
}

// =============================================================================
// Mathlib Pattern: Implication Chain
//
// Common in algebraic hierarchy proofs
// =============================================================================

/// Test: Prove implication via hypothesis chain
///
/// example (h1 : A → B) (h2 : B → C) (h3 : A) : C := by aesop
#[test]
fn test_mathlib_impl_chain() {
    let mut env = Environment::new();
    env.init_and().unwrap();
    env.init_classical().unwrap();

    let prop = Expr::prop();

    // Add A, B, C
    for name in ["A", "B", "C"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: prop.clone(),
        })
        .unwrap();
    }

    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    let c = Expr::const_(Name::from_string("C"), vec![]);

    // Goal: C
    // Context: h1 : A → B, h2 : B → C, h3 : A
    let mut state = ProofState::with_context(
        env,
        c.clone(),
        vec![
            LocalDecl {
                fvar: FVarId::new(0),
                name: "h1".to_string(),
                ty: Expr::arrow(a.clone(), b.clone()),
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(1),
                name: "h2".to_string(),
                ty: Expr::arrow(b.clone(), c.clone()),
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(2),
                name: "h3".to_string(),
                ty: a.clone(),
                value: None,
            },
        ],
    );

    let result = aesop(&mut state);

    assert!(
        result.is_ok(),
        "aesop should prove implication chain via apply h2, apply h1, exact h3"
    );
    assert!(
        state.is_complete(),
        "implication chain proof should close all goals"
    );
}

// =============================================================================
// Mathlib Pattern: Or Elimination
//
// Common in case analysis proofs
// =============================================================================

/// Test: Or elimination pattern
///
/// example (h : A ∨ B) (ha : A → C) (hb : B → C) : C := by aesop
///
/// This test verifies that aesop can use cases on Or hypotheses
/// to split into two branches and apply the appropriate implication.
#[test]
fn test_mathlib_or_elim() {
    let mut env = Environment::new();
    env.init_and().unwrap();
    env.init_classical().unwrap();

    let prop = Expr::prop();

    for name in ["A", "B", "C"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: prop.clone(),
        })
        .unwrap();
    }

    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    let c = Expr::const_(Name::from_string("C"), vec![]);
    let or = Expr::const_(Name::from_string("Or"), vec![]);

    // Goal: C
    // Context: h : A ∨ B, ha : A → C, hb : B → C
    let a_or_b = Expr::app(Expr::app(or, a.clone()), b.clone());
    let mut state = ProofState::with_context(
        env,
        c.clone(),
        vec![
            LocalDecl {
                fvar: FVarId::new(0),
                name: "h".to_string(),
                ty: a_or_b,
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(1),
                name: "ha".to_string(),
                ty: Expr::arrow(a, c.clone()),
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(2),
                name: "hb".to_string(),
                ty: Expr::arrow(b, c),
                value: None,
            },
        ],
    );

    let result = aesop(&mut state);

    assert!(
        result.is_ok(),
        "aesop should use Or.elim on h with ha and hb"
    );
    assert!(
        state.is_complete(),
        "Or elimination proof should close all goals"
    );
}

// =============================================================================
// Mathlib Pattern: Negation Introduction
//
// Used in contradiction proofs
// =============================================================================

/// Test: Prove negation by deriving False
///
/// example (h : A → B) (hnb : ¬B) : ¬A := by aesop
#[test]
fn test_mathlib_neg_intro() {
    let mut env = Environment::new();
    env.init_and().unwrap();
    env.init_classical().unwrap();

    let prop = Expr::prop();

    for name in ["A", "B"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: prop.clone(),
        })
        .unwrap();
    }

    let a = Expr::const_(Name::from_string("A"), vec![]);
    let b = Expr::const_(Name::from_string("B"), vec![]);
    let false_ = Expr::const_(Name::from_string("False"), vec![]);

    // ¬A = A → False
    let not_a = Expr::arrow(a.clone(), false_.clone());
    // ¬B = B → False
    let not_b = Expr::arrow(b.clone(), false_);

    // Goal: ¬A
    // Context: h : A → B, hnb : ¬B
    let mut state = ProofState::with_context(
        env,
        not_a,
        vec![
            LocalDecl {
                fvar: FVarId::new(0),
                name: "h".to_string(),
                ty: Expr::arrow(a.clone(), b),
                value: None,
            },
            LocalDecl {
                fvar: FVarId::new(1),
                name: "hnb".to_string(),
                ty: not_b,
                value: None,
            },
        ],
    );

    let result = aesop(&mut state);

    assert!(
        result.is_ok(),
        "aesop should prove ¬A via intro, apply hnb, apply h"
    );
    assert!(
        state.is_complete(),
        "negation introduction proof should close all goals"
    );
}

// =============================================================================
// Summary: Mathlib Aesop Usage Patterns
// =============================================================================

// Mathlib aesop patterns (Part of #15): type class resolution,
// logical reasoning, existence proofs, implication chains,
// Or elimination, contradiction proofs, constructor automation.
