// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Tier A `NNVerify.Rat.le_refl_zero` (#3551).

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::Expr;
use crate::name::Name;
use crate::tc::TypeChecker;

const TARGET: &str = "NNVerify.Rat.le_refl_zero";

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_tier_a_rat_le_refl_zero()
        .expect("init should succeed");
    env
}

#[test]
fn test_rat_le_refl_zero_registered() {
    let env = make_env();
    assert!(env.get_const(&Name::from_string(TARGET)).is_some());
    assert!(env.has_nn_verify_tier_a_rat_le_refl_zero());
}

#[test]
fn test_rat_le_refl_zero_is_theorem() {
    let env = make_env();
    let info = env.get_const(&Name::from_string(TARGET)).unwrap();
    assert_eq!(info.kind, ConstantKind::Theorem);
}

#[test]
fn test_rat_le_refl_zero_type_checks() {
    let env = make_env();
    let e = Expr::const_(Name::from_string(TARGET), vec![]);
    let tc = TypeChecker::with_mode(&env, env.mode());
    let _ = tc
        .infer_type(&e)
        .unwrap_or_else(|err| panic!("{TARGET} should type-check: {err:?}"));
}

/// #3470 Lane #2/#3 (2026-06): `NNVerify.Rat.le_refl_zero` has proof term
/// `Rat.le_refl Rat.zero`. `Rat.le_refl` — the only axiom this theorem touched —
/// has now been GENUINELY ELIMINATED to a kernel-checked constructive
/// `Declaration::Theorem` (`algebra_rat_order_proofs.rs`,
/// `λ a => @Int.le_refl (cross a a)`). The transitive axiom closure is therefore
/// now EMPTY and the honest classification is `ProofQuality::Constructive` — a
/// genuine increase in verified depth (the previously-admitted Rat ordering
/// axiom is itself now kernel-proven). No `sorry`, no `sorryAx`.
#[test]
fn test_rat_le_refl_zero_axiom_closure_is_empty_constructive() {
    use crate::env::axiom_audit::ProofQuality;
    let env = make_env();
    let deps = env
        .axiom_deps(&Name::from_string(TARGET))
        .expect("axiom_deps");
    let dep_strings: std::collections::HashSet<String> =
        deps.iter().map(|n| n.to_string()).collect();
    // No incomplete-proof / trust-marker sentinels.
    assert!(!dep_strings.contains("sorry"));
    assert!(!dep_strings.contains("sorryAx"));
    // Honest post-elimination state: empty closure, Constructive.
    assert!(
        deps.is_empty(),
        "{TARGET} reduces to the now-constructive Rat.le_refl Theorem, so its \
         axiom closure must be EMPTY; got {deps:?}"
    );
    let quality = env
        .proof_quality(&Name::from_string(TARGET))
        .expect("proof_quality");
    assert!(
        matches!(quality, ProofQuality::Constructive),
        "{TARGET} must be Constructive after the Rat.le_refl elimination, got {quality:?}"
    );
}

#[test]
fn test_rat_le_refl_zero_idempotent() {
    let mut env = Environment::new();
    env.init_nn_verify_tier_a_rat_le_refl_zero().unwrap();
    env.init_nn_verify_tier_a_rat_le_refl_zero().unwrap();
    assert!(env.has_nn_verify_tier_a_rat_le_refl_zero());
}
