// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end tests for the Lean 4 `rintro pat …` surface form.
//!
//! `rintro pat₁ pat₂ …` is exactly `intro <fresh> ; rcases <fresh> with patᵢ`
//! for each pattern, left-to-right. These tests exercise the full
//! parse -> elaborate -> kernel-type-check path: a `theorem ... := by rintro
//! …; exact …` proof is parsed by `clean-parser` (the dedicated `rintro` arm
//! captures each anonymous-constructor pattern as canonical `⟨…⟩` source text),
//! elaborated by `clean-elab` (the `rintro` compound handler `intro`s a fresh
//! binder then re-resolves it BY NAME and destructs it through the SAME
//! kernel-checked `cases`/`casesOn` engine that backs `obtain`/`rcases`), and
//! the resulting proof term is type-checked against the stated type by the
//! kernel.
//!
//! Regression for the `UnknownFVar` dangling-reference bug: the previous path
//! elaborated `⟨…⟩` as a term-mode anonymous constructor and captured an FVar id
//! from BEFORE the `intro`/`cases` mutated the local context, producing a stale
//! reference the kernel rejected. Re-resolving the introduced hypothesis by name
//! after each `intro` is what fixes it. A pattern that does not match the
//! introduced hypothesis (e.g. too many components) surfaces as an elaboration
//! error, never a panic and never a silent over-accept.

use super::common::check_and_add_decl;
use clean_kernel::{Declaration, Environment, Expr, Name};

/// Build a logic environment with And, Exists, and props P/Q/R, plus a `Nat`
/// type and a predicate over it, mirroring the prove-it surface cases.
fn setup_logic_env() -> Environment {
    let mut env = Environment::new();
    env.init_true_false().expect("init_true_false");
    env.init_and().expect("init_and");
    env.init_classical().expect("init_classical");
    env.init_exists().expect("init_exists");
    env.init_nat().expect("init_nat");
    // `Eq` backs the `⟨b, rfl⟩` substitution-pattern test.
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

    // A : Type, pr : A → Prop — for the ∃ destructure case.
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

    env
}

#[test]
fn test_rintro_and_binds_right_kernel_accepts() {
    // The confirmed repro: rintro ⟨hp, hq⟩; exact hq  on  P ∧ Q → Q.
    // Previously failed with TypeCheckFailed("UnknownFVar(...)").
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem rintro_and_right : And P Q → Q := by\n  rintro ⟨hp, hq⟩\n  exact hq",
    );
    assert!(
        result.is_ok(),
        "rintro ⟨hp, hq⟩ then `exact hq` should kernel-check, got: {result:?}"
    );
}

#[test]
fn test_rintro_and_binds_left_kernel_accepts() {
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem rintro_and_left : And P Q → P := by\n  rintro ⟨hp, hq⟩\n  exact hp",
    );
    assert!(
        result.is_ok(),
        "rintro ⟨hp, hq⟩ then `exact hp` should kernel-check, got: {result:?}"
    );
}

#[test]
fn test_rintro_rfl_pattern_substitutes_kernel_accepts() {
    // `rintro ⟨b, rfl⟩` on `∃ b, a = b → True`: intro the existential, bind `b`,
    // then the `rfl` pattern `subst`s the equation `a = b`. Goal `True` is closed
    // by `trivial`. Previously FAILED (parse error on the `rfl` keyword inside
    // `⟨⟩`). The leading `(a : Nat)` is a binder so the goal is a Π that rintro
    // first intros, then the `⟨b, rfl⟩` destructures the existential.
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem rintro_rfl (a : Nat) : Exists (fun b : Nat => Eq a b) → True := by\n  rintro ⟨b, rfl⟩\n  trivial",
    );
    assert!(
        result.is_ok(),
        "rintro ⟨b, rfl⟩ on (∃ b, a = b) → True then `trivial` should kernel-check, got: {result:?}"
    );
}

#[test]
fn test_rintro_auto_nest_triple_kernel_accepts() {
    // Flat ⟨ha, hb, hc⟩ on a right-nested 3-tuple auto-nests to ⟨ha, ⟨hb, hc⟩⟩
    // via the SAME flattening rule rcases uses.
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem rintro_nested : And P (And Q R) → R := by\n  rintro ⟨ha, hb, hc⟩\n  exact hc",
    );
    assert!(
        result.is_ok(),
        "rintro ⟨ha, hb, hc⟩ on a 3-tuple then `exact hc` should kernel-check, got: {result:?}"
    );
}

#[test]
fn test_rintro_multiple_plain_binders_kernel_accepts() {
    // Multiple plain-name patterns are sequential `intro`s.
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem rintro_plain : P → Q → P := by\n  rintro hp hq\n  exact hp",
    );
    assert!(
        result.is_ok(),
        "rintro hp hq then `exact hp` should kernel-check, got: {result:?}"
    );
}

#[test]
fn test_rintro_exists_binds_witness_kernel_accepts() {
    // rintro ⟨n, hp⟩  on  (∃ _ : Nat, P) → P; the witness `n : Nat` is bound and
    // the proof field `hp : P` discharges the goal. Mirrors the prove-it case.
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem rintro_exists : Exists (fun _ : Nat => P) → P := by\n  rintro ⟨n, hp⟩\n  exact hp",
    );
    assert!(
        result.is_ok(),
        "rintro ⟨n, hp⟩ on ∃ then `exact hp` should kernel-check, got: {result:?}"
    );
}

#[test]
fn test_rintro_too_many_components_errors_not_panics() {
    // Destructuring a 2-field And with a 3-component pattern has no sound
    // casesOn fields to bind the extra name. This must surface as an
    // elaboration error (not a panic) and must NOT yield a kernel-accepted
    // proof: a wrong / over-long pattern can never silently succeed.
    let mut env = setup_logic_env();
    let result = check_and_add_decl(
        &mut env,
        "theorem rintro_too_many : And P Q → Q := by\n  rintro ⟨hp, hq, hr⟩\n  exact hq",
    );
    assert!(
        result.is_err(),
        "rintro ⟨hp, hq, hr⟩ on a 2-field And must error, not silently succeed: {result:?}"
    );
}
