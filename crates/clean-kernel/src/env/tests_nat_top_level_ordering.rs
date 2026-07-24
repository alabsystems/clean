// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for top-level `Nat.*` ordering primitives promoted from Axiom to
//! constructive Theorem (#3599, Part of #3551).
//!
//! Verifies that each of the five theorems is:
//! 1. Registered as `Declaration::Theorem` (not `Declaration::Axiom`).
//! 2. Has a type-checking proof term.
//! 3. Has an empty domain-specific axiom closure.
//! 4. Uses `Nat.le.rec` or `Nat.rec` in its proof term (not a trivial axiom ref).
//! 5. `init_nat_top_level_ordering` is idempotent.

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::Expr;
use crate::name::Name;
use crate::tc::TypeChecker;

const TARGETS: &[&str] = &[
    "Nat.le_refl",
    "Nat.succ_le_succ",
    "Nat.succ_lt_succ",
    "Nat.le_of_lt",
    "Nat.zero_lt_succ",
];

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nat_top_level_ordering()
        .expect("top-level Nat ordering init should succeed");
    env
}

#[test]
fn test_nat_top_level_ordering_all_registered() {
    let env = make_env();
    for target in TARGETS {
        assert!(
            env.get_const(&Name::from_string(target)).is_some(),
            "{target} must be registered"
        );
    }
}

#[test]
fn test_nat_top_level_ordering_are_theorems_not_axioms() {
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
fn test_nat_top_level_ordering_type_checks() {
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
fn test_nat_top_level_ordering_axiom_closures_empty() {
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
fn test_nat_top_level_ordering_proofs_use_nat_rec() {
    // Each of the five theorem proof terms should reference either
    // `Nat.le.rec` (induction on Nat.le) or `Nat.rec` (induction on Nat)
    // in their value. `Nat.le_refl` is the exception — it's a direct
    // application of the `Nat.le.refl` constructor, no recursion needed.
    let env = make_env();
    let expect_rec: &[(&str, &[&str])] = &[
        ("Nat.le_refl", &["Nat.le.refl"]),
        ("Nat.succ_le_succ", &["Nat.le.rec"]),
        ("Nat.succ_lt_succ", &["Nat.le.rec"]),
        ("Nat.le_of_lt", &["Nat.le.rec"]),
        ("Nat.zero_lt_succ", &["Nat.rec"]),
    ];

    for (target, required_any) in expect_rec {
        let info = env
            .get_const(&Name::from_string(target))
            .unwrap_or_else(|| panic!("{target} must be registered"));
        assert_eq!(info.kind, ConstantKind::Theorem, "{target} must be Theorem");
        let value = info
            .value
            .as_ref()
            .unwrap_or_else(|| panic!("{target} must carry a proof term"));
        // The `Display` impl for Expr prints dotted names as `Nat.le.refl`
        // whereas `Debug` nests each `Name` segment as a separate struct.
        // Use Display so the substring match sees the qualified name as-is.
        let text = format!("{value}");
        let found = required_any.iter().any(|needle| text.contains(needle));
        assert!(
            found,
            "{target} proof must reference one of {required_any:?}; got term = {text}"
        );
    }
}

#[test]
fn test_nat_top_level_ordering_idempotent() {
    let mut env = Environment::new();
    env.init_nat_top_level_ordering().unwrap();
    env.init_nat_top_level_ordering().unwrap();
    assert!(env.has_nat_top_level_ordering());
    for target in TARGETS {
        assert!(env.get_const(&Name::from_string(target)).is_some());
    }
}
