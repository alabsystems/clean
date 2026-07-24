// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Guards that the `Int.dist` metric axioms are ELIMINATED:
//! - `Int.dist` is now a reducible `Declaration::Definition`
//!   (`λ a b => Int.abs (Int.sub a b)`), not an opaque `Declaration::Axiom`.
//! - `Int.dist_eq_abs_sub` is a Constructive Theorem (`@Eq.refl` — `Int.dist`
//!   reduces to `Int.abs (Int.sub a b)`).
//! - `Int.dist_nonneg` is a Constructive Theorem (`Int.abs_nonneg (Int.sub a b)`).

use crate::env::axiom_audit::ProofQuality;
use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::Expr;
use crate::name::Name;
use crate::tc::TypeChecker;

fn env() -> Environment {
    let mut env = Environment::new();
    env.init_int_dist().expect("init_int_dist should succeed");
    env
}

#[test]
fn test_int_dist_is_reducible_definition_not_axiom() {
    let env = env();
    let info = env
        .get_const(&Name::from_string("Int.dist"))
        .expect("Int.dist registered");
    assert_eq!(
        info.kind,
        ConstantKind::Definition,
        "Int.dist must be a reducible Definition (eliminated as an opaque axiom), got {:?}",
        info.kind
    );
    assert!(info.value.is_some(), "Int.dist Definition must have a body");
    // Kernel type-checks the body.
    let tc = TypeChecker::with_mode(&env, env.mode());
    let _ = tc
        .infer_type(&Expr::const_(Name::from_string("Int.dist"), vec![]))
        .expect("Int.dist should kernel-type-check");
}

fn assert_constructive_theorem(env: &Environment, name: &str) {
    let info = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} should be registered"));
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "{name} must be a kernel-checked Theorem, got {:?}",
        info.kind
    );
    assert!(info.value.is_some(), "{name} Theorem must retain its value");
    let tc = TypeChecker::with_mode(env, env.mode());
    let _ = tc
        .infer_type(&Expr::const_(Name::from_string(name), vec![]))
        .unwrap_or_else(|err| panic!("{name} should kernel-type-check, got {err:?}"));
    let q = env
        .proof_quality(&Name::from_string(name))
        .expect("proof_quality");
    assert!(
        matches!(q, ProofQuality::Constructive),
        "{name} must be Constructive (empty domain-axiom closure), got {q:?}"
    );
}

#[test]
fn test_int_dist_eq_abs_sub_is_constructive_theorem() {
    assert_constructive_theorem(&env(), "Int.dist_eq_abs_sub");
}

#[test]
fn test_int_dist_nonneg_is_constructive_theorem() {
    assert_constructive_theorem(&env(), "Int.dist_nonneg");
}
