// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end tests for the Lean 4 `rcases h with ⟨pat⟩` surface form.
//!
//! These tests exercise the full parse -> elaborate -> kernel-type-check path:
//! a `theorem ... := by rcases ... ; exact ...` proof is parsed by
//! `clean-parser` (the dedicated `rcases` arm captures the `with`-clause
//! pattern, reusing `obtain`'s anonymous-constructor reader), elaborated by
//! `clean-elab` (the `rcases` compound handler resolves the scrutinee to an
//! EXISTING hypothesis name and destructs it through the kernel-checked
//! `cases`/`casesOn` engine — the same engine that backs `obtain`/`rintro`),
//! and the resulting proof term is type-checked against the stated type by the
//! kernel.
//!
//! Unlike `obtain`, `rcases` does NOT introduce a copy: it destructures the
//! hypothesis in place. A pattern/type mismatch surfaces as an elaboration
//! error, never a panic, and the goal is only ever closed via the
//! kernel-checked path.

use super::common::check_and_add_decl;
use clean_kernel::{Declaration, Environment, Expr, Name};

/// Build a logic environment with And, Exists, props P/Q/R, a type A with a
/// predicate `pr : A → Prop`, and an Atom prop for the mismatch test.
fn setup_logic_env() -> Environment {
    let mut env = Environment::new();
    env.init_true_false().expect("init_true_false");
    env.init_and().expect("init_and");
    env.init_classical().expect("init_classical");
    env.init_exists().expect("init_exists");
    // `Nat`/`Eq` back the `⟨b, rfl⟩` substitution-pattern test.
    env.init_nat().expect("init_nat");
    env.init_eq().expect("init_eq");

    let prop = Expr::prop();
    for name in ["P", "Q", "R"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: prop.clone(),
        })
        .expect("add prop axiom");
    }

    // A : Type, pr : A → Prop
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("add A");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("pr"),
        level_params: vec![],
        type_: Expr::arrow(Expr::const_(Name::from_string("A"), vec![]), Expr::prop()),
    })
    .expect("add pr");

    // A non-pair proposition `Atom : Prop`, for the mismatch test.
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Atom"),
        level_params: vec![],
        type_: prop.clone(),
    })
    .expect("add Atom");

    env
}

#[test]
fn test_rcases_and_binds_right_kernel_accepts() {
    // The confirmed repro: rcases h with ⟨hp, hq⟩; exact hq  on  h : P ∧ Q ⊢ Q.
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem rcases_and_right (h : And P Q) : Q := by\n  rcases h with ⟨hp, hq⟩\n  exact hq",
    );
    assert!(
        result.is_ok(),
        "rcases h with ⟨hp, hq⟩ then `exact hq` should kernel-check, got: {result:?}"
    );
}

#[test]
fn test_rcases_and_binds_left_kernel_accepts() {
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem rcases_and_left (h : And P Q) : P := by\n  rcases h with ⟨hp, hq⟩\n  exact hp",
    );
    assert!(
        result.is_ok(),
        "rcases h with ⟨hp, hq⟩ then `exact hp` should kernel-check, got: {result:?}"
    );
}

#[test]
fn test_rcases_nested_triple_kernel_accepts() {
    // Nested ⟨a, b, c⟩ on a 3-tuple (right-nested And) ⊢ R.
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem rcases_nested (h : And P (And Q R)) : R := by\n  rcases h with ⟨a, b, c⟩\n  exact c",
    );
    assert!(
        result.is_ok(),
        "rcases h with ⟨a, b, c⟩ on a 3-tuple then `exact c` should kernel-check, got: {result:?}"
    );
}

#[test]
fn test_rcases_rfl_pattern_substitutes_kernel_accepts() {
    // `rcases h with ⟨b, rfl⟩` on `h : ∃ b, a = b`: binds `b`, then the `rfl`
    // pattern `subst`s the equation `a = b`. Goal `True` closed by `trivial`.
    // Previously FAILED (parse error on the `rfl` keyword token inside `⟨⟩`).
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem rcases_rfl (a : Nat) (h : Exists (fun b : Nat => Eq a b)) : True := by\n  rcases h with ⟨b, rfl⟩\n  trivial",
    );
    assert!(
        result.is_ok(),
        "rcases h with ⟨b, rfl⟩ on ∃ b, a = b then `trivial` should kernel-check, got: {result:?}"
    );
}

#[test]
fn test_rcases_nested_explicit_kernel_accepts() {
    // Fully-parenthesized nested pattern ⟨a, ⟨b, c⟩⟩.
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem rcases_nested2 (h : And P (And Q R)) : R := by\n  rcases h with ⟨a, ⟨b, c⟩⟩\n  exact c",
    );
    assert!(
        result.is_ok(),
        "rcases h with ⟨a, ⟨b, c⟩⟩ then `exact c` should kernel-check, got: {result:?}"
    );
}

#[test]
fn test_rcases_exists_binds_witness_kernel_accepts() {
    // rcases h with ⟨n, hn⟩  on  h : ∃ x, pr x; rebuild via ⟨n, hn⟩.
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem rcases_exists (h : Exists (fun x : A => pr x)) : Exists (fun x : A => pr x) := by\n  rcases h with ⟨n, hn⟩\n  exact ⟨n, hn⟩",
    );
    assert!(
        result.is_ok(),
        "rcases h with ⟨n, hn⟩ on ∃ then rebuild should kernel-check, got: {result:?}"
    );
}

#[test]
fn test_rcases_too_many_components_errors_not_panics() {
    // Destructuring a 2-field And with a 3-component pattern has no sound
    // casesOn fields to bind the extra name. This must surface as an
    // elaboration error (not a panic) and must NOT yield a kernel-accepted
    // proof. Wrong destructuring must fail.
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem rcases_too_many (h : And P Q) : P := by\n  rcases h with ⟨a, b, c⟩\n  exact a",
    );
    assert!(
        result.is_err(),
        "rcases ⟨a, b, c⟩ on a 2-field And must error, not silently succeed: {result:?}"
    );
}

#[test]
fn test_rcases_pattern_type_mismatch_errors_not_panics() {
    // Destructuring a non-pair hypothesis `h : Atom` with a 2-field tuple must
    // error, mirroring the obtain mismatch test.
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem rcases_mismatch (h : Atom) : P := by\n  rcases h with ⟨a, b⟩\n  exact a",
    );
    assert!(
        result.is_err(),
        "rcases ⟨a, b⟩ on a non-pair hypothesis must error, not silently succeed: {result:?}"
    );
}

#[test]
fn test_cases_on_eq_hypothesis_substitutes_kernel_accepts() {
    // `cases h` on `h : a = b` IS `subst` in Lean 4. Previously the generic
    // N-constructor `casesOn`-motive path leaked an unbound sentinel FVar and
    // left an unapplied Pi where a proof of the goal was required, so this
    // FAILED with a `TypeMismatch`. It now routes through the kernel-checked
    // `subst` machinery: after substituting `a := b` the goal `b = a` becomes
    // `b = b`, which `rfl` closes. The resulting proof term is kernel-rechecked
    // by `add_decl`, so acceptance here is genuine, not a silent over-accept.
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem cases_eq_flip (a b : Nat) (h : Eq a b) : Eq b a := by\n  cases h\n  rfl",
    );
    assert!(
        result.is_ok(),
        "cases h on h : a = b then `rfl` should kernel-check (routes to subst), got: {result:?}"
    );
}

#[test]
fn test_cases_on_eq_hypothesis_same_direction_kernel_accepts() {
    // Same-direction goal: `cases h` on `h : a = b` with goal `a = b`. After
    // substituting `a := b` the goal becomes `b = b`, closed by `rfl`.
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem cases_eq_same (a b : Nat) (h : Eq a b) : Eq a b := by\n  cases h\n  rfl",
    );
    assert!(
        result.is_ok(),
        "cases h on h : a = b with same-direction goal then `rfl` should kernel-check, got: {result:?}"
    );
}

#[test]
fn test_cases_on_eq_unclosed_goal_errors_not_panics() {
    // Without the closing `rfl`, `cases h` on `h : a = b` (goal `b = a`) leaves
    // the substituted goal `b = b` open. This MUST surface as an unsolved-goal
    // elaboration error (not a panic, not a silent over-accept), proving the
    // routing is fail-closed and does not fabricate a proof.
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem cases_eq_open (a b : Nat) (h : Eq a b) : Eq b a := by\n  cases h",
    );
    assert!(
        result.is_err(),
        "cases h on h : a = b WITHOUT a closing tactic must error (unsolved goal), got: {result:?}"
    );
}

#[test]
fn test_cases_on_eq_wrong_goal_errors_not_panics() {
    // After `cases h` on `h : a = b` (substituting `a := b`), the goal `b = c`
    // becomes `a = c` (three distinct variables) which `rfl` cannot close. This
    // MUST error, confirming the substituted goal is genuinely kernel-checked
    // and a mismatched `rfl` is rejected rather than over-accepted.
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem cases_eq_wrong (a b c : Nat) (h : Eq a b) : Eq b c := by\n  cases h\n  rfl",
    );
    assert!(
        result.is_err(),
        "cases h then `rfl` on an unclosable goal `a = c` must error, got: {result:?}"
    );
}
