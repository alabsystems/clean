// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the mixed `Nat.*` transitivity lemmas promoted from Axiom to
//! constructive Theorem (#3551).
//!
//! Pins that each of the two demoted lemmas is:
//! 1. Registered as `Declaration::Theorem` (not `Declaration::Axiom`).
//! 2. Carries a proof term that passes the kernel type-check.
//! 3. Has an empty domain-specific axiom closure (no `sorry`/`sorryAx`/domain
//!    axioms), i.e. `ProofQuality::Constructive`.
//! 4. References `Nat.le_trans` in its proof term (not a trivial restatement).
//! 5. The owning init functions remain idempotent.
//!
//! - `Nat.lt_of_lt_of_le` — registered by `init_nat_trans_lt_le_lt`.
//! - `Nat.lt_of_le_of_lt` — registered by `init_nat_trans_le_lt_lt`.

use crate::env::types::ConstantKind;
use crate::env::{Environment, ProofQuality};
use crate::expr::Expr;
use crate::name::Name;
use crate::tc::TypeChecker;

const TARGETS: &[&str] = &["Nat.lt_of_lt_of_le", "Nat.lt_of_le_of_lt"];

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nat_trans_lt_le_lt()
        .expect("init_nat_trans_lt_le_lt should succeed");
    env.init_nat_trans_le_lt_lt()
        .expect("init_nat_trans_le_lt_lt should succeed");
    env
}

#[test]
fn test_mixed_trans_lemmas_are_theorems_not_axioms() {
    let env = make_env();
    for target in TARGETS {
        let info = env
            .get_const(&Name::from_string(target))
            .unwrap_or_else(|| panic!("{target} must be registered"));
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
fn test_mixed_trans_lemmas_type_check() {
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
fn test_mixed_trans_lemmas_axiom_closures_empty() {
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
            "{target} must have empty domain-axiom closure; got {dep_names:?}"
        );
    }
}

#[test]
fn test_mixed_trans_lemmas_proof_quality_constructive() {
    let env = make_env();
    for target in TARGETS {
        let quality = env
            .proof_quality(&Name::from_string(target))
            .unwrap_or_else(|| panic!("proof_quality must succeed for {target}"));
        assert_eq!(
            quality,
            ProofQuality::Constructive,
            "{target} must be Constructive; got {quality:?}"
        );
    }
}

#[test]
fn test_mixed_trans_lemmas_reference_le_trans() {
    // Each proof chains through `Nat.le_trans`; ensure the term actually
    // references it rather than being a trivial axiom-wrapping restatement.
    let env = make_env();
    for target in TARGETS {
        let info = env
            .get_const(&Name::from_string(target))
            .unwrap_or_else(|| panic!("{target} must be registered"));
        let value = info
            .value
            .as_ref()
            .unwrap_or_else(|| panic!("{target} must carry a proof term"));
        let text = format!("{value}");
        assert!(
            text.contains("Nat.le_trans"),
            "{target} proof must reference Nat.le_trans; got term = {text}"
        );
    }
}

#[test]
fn test_lt_of_le_of_lt_references_succ_le_succ() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("Nat.lt_of_le_of_lt"))
        .expect("Nat.lt_of_le_of_lt must be registered");
    let value = info.value.as_ref().expect("must carry a proof term");
    let text = format!("{value}");
    assert!(
        text.contains("Nat.succ_le_succ"),
        "Nat.lt_of_le_of_lt proof must reference Nat.succ_le_succ; got term = {text}"
    );
}

#[test]
fn test_mixed_trans_init_idempotent() {
    let mut env = Environment::new();
    env.init_nat_trans_lt_le_lt().unwrap();
    env.init_nat_trans_lt_le_lt().unwrap();
    env.init_nat_trans_le_lt_lt().unwrap();
    env.init_nat_trans_le_lt_lt().unwrap();
    assert!(env.has_nat_trans_lt_le_lt());
    assert!(env.has_nat_trans_le_lt_lt());
    for target in TARGETS {
        assert!(
            env.get_const(&Name::from_string(target)).is_some(),
            "{target} must remain registered after repeated init"
        );
    }
}
