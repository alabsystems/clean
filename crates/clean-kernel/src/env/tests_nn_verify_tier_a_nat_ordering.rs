// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Tier A Batch 3 Nat ordering primitives (#3551 / #3599).
//!
//! Verifies that each of the four theorems is:
//! 1. Registered as `Declaration::Theorem` (not `Declaration::Axiom`).
//! 2. Has a type-checking proof term.
//! 3. Has an empty domain-specific axiom closure.
//! 4. `init_nn_verify_tier_a_nat_ordering` is idempotent.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::Expr;
use crate::name::Name;
use crate::tc::TypeChecker;

const TARGETS: &[&str] = &[
    "NNVerify.Nat.succ_le_succ",
    "NNVerify.Nat.zero_le",
    "NNVerify.Nat.le_of_lt",
    "NNVerify.Nat.lt_of_succ_le",
];

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_tier_a_nat_ordering()
        .expect("tier A nat ordering init should succeed");
    env
}

#[test]
fn test_tier_a_nat_ordering_all_registered() {
    let env = make_env();
    for target in TARGETS {
        assert!(
            env.get_const(&Name::from_string(target)).is_some(),
            "{target} must be registered"
        );
    }
}

#[test]
fn test_tier_a_nat_ordering_are_theorems_not_axioms() {
    let env = make_env();
    for target in TARGETS {
        let info = env.get_const(&Name::from_string(target)).unwrap();
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "{target} must be Theorem, got {:?}",
            info.kind
        );
        assert!(
            info.value.is_some(),
            "{target} must carry a proof term (not a bare axiom)"
        );
    }
}

#[test]
fn test_tier_a_nat_ordering_type_checks() {
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    for target in TARGETS {
        let e = Expr::const_(Name::from_string(target), vec![]);
        let _ = tc
            .infer_type(&e)
            .unwrap_or_else(|err| panic!("{target} should type-check: {err:?}"));
    }
}

#[test]
fn test_tier_a_nat_ordering_axiom_closures_empty() {
    let env = make_env();
    for target in TARGETS {
        let deps = env
            .axiom_deps(&Name::from_string(target))
            .unwrap_or_else(|| panic!("axiom_deps must succeed for {target}"));
        let dep_names: std::collections::HashSet<String> =
            deps.iter().map(|n| n.to_string()).collect();
        assert!(
            !dep_names.contains("sorry"),
            "{target} must not depend on sorry; closure = {dep_names:?}"
        );
        assert!(
            !dep_names.contains("sorryAx"),
            "{target} must not depend on sorryAx; closure = {dep_names:?}"
        );
        assert!(
            dep_names.is_empty(),
            "{target} must have empty axiom closure; got {dep_names:?}"
        );
    }
}

#[test]
fn test_tier_a_nat_ordering_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_tier_a_nat_ordering().unwrap();
    env.init_nn_verify_tier_a_nat_ordering().unwrap();
    assert!(env.has_nn_verify_tier_a_nat_ordering());
    for target in TARGETS {
        assert!(env.get_const(&Name::from_string(target)).is_some());
    }
}
