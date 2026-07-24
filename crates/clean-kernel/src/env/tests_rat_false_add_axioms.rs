// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! WS-A ATOMIC LIVE SWITCH regression guards.
//!
//! HISTORY: `Rat.add_le_add_left` and `Rat.le_add_of_nonneg_right` were
//! admitted axioms that were PROVABLY FALSE on the OLD free-inductive
//! `Rat.mk : Int → Nat` carrier (no `denom > 0` invariant): a `denom = 0`
//! representative collapsed `Rat.add`'s denominator, so the bare numerators were
//! compared at effective denominator 1, producing a hard false inequality
//! (`Int.le 2 1` / `Int.le 1 0`).
//!
//! WS-A made the live `Rat` the QUOTIENT carrier `Rat := Quot Rat.Raw.Equiv`,
//! which identifies all representatives of a fraction. Over the quotient these
//! two propositions are TRUE and are now GENUINE kernel-checked
//! `Declaration::Theorem`s, each `ProofQuality::Constructive` (transitive axiom
//! closure ⊆ FOUNDATIONAL: only `Quot.sound` / `propext`).
//!
//! The old counterexamples no longer expose unsoundness — the offending classes
//! (`mk 2 0` vs `mk 1 0`, etc.) are now `Quot.sound`-equal — so these tests are
//! flipped to PIN the eliminated state: each name is a Constructive Theorem.

use super::Environment;
use crate::env::types::ConstantKind;
use crate::env::ProofQuality;
use crate::name::Name;
use crate::tc::TypeChecker;

fn env() -> Environment {
    let mut env = Environment::new();
    env.init_rat_ordered_field_axioms()
        .expect("init_rat_ordered_field_axioms");
    env
}

/// Assert `name` is a kernel-checked `Constructive` Theorem (axiom closure ⊆
/// FOUNDATIONAL), and that it kernel-type-checks.
fn assert_constructive_theorem(env: &Environment, name: &str) {
    let info = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} registered"));
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "{name} is now a genuine quotient Theorem (was a FALSE-on-free-carrier \
         admitted Axiom before WS-A); got {:?}",
        info.kind
    );
    assert!(
        info.value.is_some(),
        "{name} Theorem must retain a proof value",
    );
    let tc = TypeChecker::with_mode(env, env.mode());
    let _ = tc
        .infer_type(&crate::expr::Expr::const_(Name::from_string(name), vec![]))
        .unwrap_or_else(|e| panic!("{name} must kernel-type-check: {e:?}"));
    let q = env
        .proof_quality(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} proof_quality"));
    assert!(
        matches!(q, ProofQuality::Constructive),
        "{name} must be Constructive over the quotient (closure ⊆ FOUNDATIONAL: \
         Quot.sound / propext are foundational), got {q:?}",
    );
}

/// `Rat.add_le_add_left` is now a Constructive quotient Theorem (formerly a
/// FALSE admitted Axiom on the free carrier).
#[test]
fn test_add_le_add_left_is_now_constructive_theorem() {
    let env = env();
    assert_constructive_theorem(&env, "Rat.add_le_add_left");
}

/// `Rat.le_add_of_nonneg_right` is now a Constructive quotient Theorem.
#[test]
fn test_le_add_of_nonneg_right_is_now_constructive_theorem() {
    let env = env();
    assert_constructive_theorem(&env, "Rat.le_add_of_nonneg_right");
}

/// The companion order/equality `Rat.*` facts that were also FALSE on the free
/// carrier (`Rat.le_antisymm`) are likewise Constructive quotient Theorems.
#[test]
fn test_le_antisymm_is_now_constructive_theorem() {
    let mut env = Environment::new();
    env.init_rat_linear_order().expect("init_rat_linear_order");
    assert_constructive_theorem(&env, "Rat.le_antisymm");
}
