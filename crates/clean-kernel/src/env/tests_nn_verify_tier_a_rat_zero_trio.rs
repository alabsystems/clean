// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the Tier A "zero trio" Rat scalar lemma (#3551).
//!
//! ## What landed
//!
//! - `NNVerify.Rat.neg_zero_zero : Rat.neg Rat.zero = Rat.zero`
//!   — proof term: `@Eq.refl.{1} Rat Rat.zero`.
//!     Kernel δι reduces both sides to the common normal form
//!     `Rat.mk (Int.ofNat Nat.zero) (Nat.succ Nat.zero)`.
//!     Non-foundational axiom closure is EMPTY.
//!
//! ## What is blocked
//!
//! - `NNVerify.Rat.sub_zero_self : ∀ x : Rat, Rat.sub x Rat.zero = x`.
//!   The only viable chain proof needs `Rat.add_zero x` to finish, and
//!   `Rat.add_zero` (demoted to Theorem in #3581 Tranche B) transitively
//!   depends on Int/Nat domain axioms `Int.add_zero`, `Int.mul_one`,
//!   `Int.zero_mul`, `Nat.mul_one` — none are in `FOUNDATIONAL_AXIOMS`.
//!   A pure `Eq.refl` proof is rejected because `Rat.add x ...` on a
//!   generic `x` does not δι-reduce (requires structure-eta on an abstract
//!   `Rat`, which does not close without the field axioms).
//!   DEFERRED until the Int/Nat primitives ratchet admits these four
//!   axioms (or each gets promoted to a Theorem with empty closure).
//!
//! - `NNVerify.Rat.abs_zero_zero : Rat.abs Rat.zero = Rat.zero`.
//!   `Rat.abs` was demoted to `Declaration::Opaque` (body `fun a => a`) in
//!   #3565 (MASQUERADE fix), so `Rat.abs` does not δ-reduce. The only
//!   available fact on zero is the non-foundational axiom `Rat.abs_zero`,
//!   so any Theorem wrapping it inherits a non-empty domain closure.
//!   DEFERRED until `Rat.abs` is re-defined constructively.
//!
//! Both blockers are reported in the accompanying commit's `## Next`
//! section and tracked on issue #3551.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::Expr;
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_tier_a_rat_neg_zero_zero()
        .expect("init neg_zero_zero");
    env
}

const TARGETS: &[&str] = &["NNVerify.Rat.neg_zero_zero"];

#[test]
fn test_zero_trio_all_registered() {
    let env = make_env();
    for target in TARGETS {
        assert!(
            env.get_const(&Name::from_string(target)).is_some(),
            "{target} should be registered"
        );
    }
}

#[test]
fn test_zero_trio_has_flags() {
    let env = make_env();
    assert!(env.has_nn_verify_tier_a_rat_neg_zero_zero());
}

#[test]
fn test_zero_trio_all_are_theorems_not_axioms() {
    let env = make_env();
    for target in TARGETS {
        let info = env
            .get_const(&Name::from_string(target))
            .unwrap_or_else(|| panic!("{target} should be registered"));
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "{target} should be ConstantKind::Theorem, not Axiom"
        );
    }
}

#[test]
fn test_zero_trio_all_type_check() {
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    for target in TARGETS {
        let e = Expr::const_(Name::from_string(target), vec![]);
        let _ty = tc
            .infer_type(&e)
            .unwrap_or_else(|err| panic!("{target} should type-check: {err:?}"));
    }
}

#[test]
fn test_zero_trio_empty_non_foundational_axiom_closure() {
    let env = make_env();
    for target in TARGETS {
        let deps = env
            .axiom_deps(&Name::from_string(target))
            .unwrap_or_else(|| panic!("{target} axiom_deps should be available"));
        let deps_str: std::collections::HashSet<String> =
            deps.iter().map(|n| n.to_string()).collect();
        assert!(
            !deps_str.contains("sorry"),
            "{target} must not depend on sorry"
        );
        assert!(
            !deps_str.contains("sorryAx"),
            "{target} must not depend on sorryAx"
        );
        assert!(
            deps_str.is_empty(),
            "{target} non-foundational closure should be empty; got {deps_str:?}"
        );
    }
}

#[test]
fn test_zero_trio_all_idempotent() {
    let mut env = Environment::new();
    for _ in 0..2 {
        env.init_nn_verify_tier_a_rat_neg_zero_zero().unwrap();
    }
    for target in TARGETS {
        assert!(env.get_const(&Name::from_string(target)).is_some());
    }
}
