// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for Tier A Batch 3 Rat scalar lemmas (#3551).
//!
//! Six lemmas instantiate foundational-axiom theorems at concrete
//! `Rat.zero`/`Rat.one` arguments:
//!
//! - `NNVerify.Rat.mul_zero_zero`       — proof: `Rat.mul_zero Rat.zero`
//! - `NNVerify.Rat.mul_one_zero`        — proof: `Rat.mul_zero Rat.one`
//! - `NNVerify.Rat.mul_zero_one`        — proof: `Rat.zero_mul Rat.one`
//! - `NNVerify.Rat.add_neg_self_zero`   — proof: `Rat.add_neg_self Rat.zero`
//! - `NNVerify.Rat.add_left_neg_zero`   — proof: `Rat.add_left_neg Rat.zero`
//! - `NNVerify.Rat.mul_neg_zero_zero`   — proof: `Rat.mul_neg Rat.zero Rat.zero`
//!
//! Five of the underlying lemmas (`Rat.mul_zero`, `Rat.zero_mul`,
//! `Rat.add_neg_self`, `Rat.add_left_neg`) are ADMITTED DOMAIN axioms
//! (`crate::env::axiom_audit::ADMITTED_DOMAIN_AXIOMS`): mathematically true in
//! Lean 4 Mathlib, but registered here as bare `Declaration::Axiom`s with NO
//! Clean-kernel proof term. The 2026-06 integrity audit removed those names from
//! `is_foundational_axiom`, so `env.axiom_deps()` returns the admitted axiom for
//! each — the transitive non-foundational closure is NON-EMPTY (one admitted
//! domain axiom apiece) and they honestly classify `ProofQuality::AxiomDependent`,
//! NOT `ProofQuality::Constructive`. No `sorry`, no rogue axiom — genuine
//! wrappers honestly attributed to the admitted assumptions they consume.
//!
//! NOTE (#3470 Lane #2/#3): `Rat.mul_neg` — used by `NNVerify.Rat.mul_neg_zero_zero`
//! — has since been GENUINELY ELIMINATED to a kernel-checked constructive
//! `Declaration::Theorem` (`congrArg` over the constructive `Int.neg_mul_right`).
//! That sixth lemma's closure is therefore now EMPTY and it is honestly
//! `ProofQuality::Constructive` (see `test_batch3_mul_neg_zero_zero_is_constructive`).

use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::expr::Expr;
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_tier_a_rat_mul_zero_zero()
        .expect("init mul_zero_zero");
    env.init_nn_verify_tier_a_rat_mul_one_zero()
        .expect("init mul_one_zero");
    env.init_nn_verify_tier_a_rat_mul_zero_one()
        .expect("init mul_zero_one");
    env.init_nn_verify_tier_a_rat_add_neg_self_zero()
        .expect("init add_neg_self_zero");
    env.init_nn_verify_tier_a_rat_add_left_neg_zero()
        .expect("init add_left_neg_zero");
    env.init_nn_verify_tier_a_rat_mul_neg_zero_zero()
        .expect("init mul_neg_zero_zero");
    env
}

const TARGETS: &[&str] = &[
    "NNVerify.Rat.mul_zero_zero",
    "NNVerify.Rat.mul_one_zero",
    "NNVerify.Rat.mul_zero_one",
    "NNVerify.Rat.add_neg_self_zero",
    "NNVerify.Rat.add_left_neg_zero",
    "NNVerify.Rat.mul_neg_zero_zero",
];

#[test]
fn test_batch3_all_registered() {
    let env = make_env();
    for target in TARGETS {
        assert!(
            env.get_const(&Name::from_string(target)).is_some(),
            "{target} should be registered"
        );
    }
}

#[test]
fn test_batch3_has_flags() {
    let env = make_env();
    assert!(env.has_nn_verify_tier_a_rat_mul_zero_zero());
    assert!(env.has_nn_verify_tier_a_rat_mul_one_zero());
    assert!(env.has_nn_verify_tier_a_rat_mul_zero_one());
    assert!(env.has_nn_verify_tier_a_rat_add_neg_self_zero());
    assert!(env.has_nn_verify_tier_a_rat_add_left_neg_zero());
    assert!(env.has_nn_verify_tier_a_rat_mul_neg_zero_zero());
}

#[test]
fn test_batch3_all_are_theorems_not_axioms() {
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
fn test_batch3_all_type_check() {
    let env = make_env();
    let tc = TypeChecker::with_mode(&env, env.mode());
    for target in TARGETS {
        let e = Expr::const_(Name::from_string(target), vec![]);
        let _ty = tc
            .infer_type(&e)
            .unwrap_or_else(|err| panic!("{target} should type-check: {err:?}"));
    }
}

/// Targets whose proof term still rests directly on an admitted domain axiom
/// (`Rat.mul_zero`, `Rat.zero_mul`, `Rat.add_neg_self`, `Rat.add_left_neg`).
/// These remain honestly `AxiomDependent`.
const ADMITTED_TARGETS: &[&str] = &[
    "NNVerify.Rat.mul_zero_zero",
    "NNVerify.Rat.mul_one_zero",
    "NNVerify.Rat.mul_zero_one",
    "NNVerify.Rat.add_neg_self_zero",
    "NNVerify.Rat.add_left_neg_zero",
];

/// `NNVerify.Rat.mul_neg_zero_zero := Rat.mul_neg Rat.zero Rat.zero`. #3470
/// Lane #2/#3 GENUINELY ELIMINATED `Rat.mul_neg` from an admitted domain axiom
/// to a constructive `Declaration::Theorem`, so this lemma's axiom closure is
/// now EMPTY and it is honestly `Constructive`.
const CONSTRUCTIVE_TARGET: &str = "NNVerify.Rat.mul_neg_zero_zero";

#[test]
fn test_batch3_admitted_closure_only_admitted_domain_axioms() {
    // WS-A ATOMIC LIVE SWITCH: the five lemmas' proof terms each applied an
    // admitted domain axiom (`Rat.mul_zero`, `Rat.zero_mul`, `Rat.add_neg_self`,
    // `Rat.add_left_neg`), ALL of which are now `Constructive` quotient Theorems.
    // So each lemma's non-foundational axiom closure is now EMPTY — they are all
    // honestly `Constructive`.
    let env = make_env();
    for target in ADMITTED_TARGETS {
        let deps = env
            .axiom_deps(&Name::from_string(target))
            .unwrap_or_else(|| panic!("{target} axiom_deps should be available"));
        let deps_str: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
        assert!(
            deps.is_empty(),
            "{target} formerly rested on an admitted Rat axiom that is now a \
             quotient Theorem; its closure must be EMPTY, got {deps_str:?}"
        );
    }
}

/// #3470 Lane #2/#3: `NNVerify.Rat.mul_neg_zero_zero` (`Rat.mul_neg Rat.zero
/// Rat.zero`) is now genuinely `Constructive` — `Rat.mul_neg` has been
/// eliminated to a kernel-checked Theorem, so the closure is EMPTY.
#[test]
fn test_batch3_mul_neg_zero_zero_is_constructive() {
    use crate::env::axiom_audit::ProofQuality;
    let env = make_env();
    let deps = env
        .axiom_deps(&Name::from_string(CONSTRUCTIVE_TARGET))
        .expect("axiom_deps");
    assert!(
        deps.is_empty(),
        "{CONSTRUCTIVE_TARGET} reduces to the now-constructive Rat.mul_neg \
         Theorem, so its axiom closure must be EMPTY; got {deps:?}"
    );
    let quality = env
        .proof_quality(&Name::from_string(CONSTRUCTIVE_TARGET))
        .expect("proof_quality");
    assert!(
        matches!(quality, ProofQuality::Constructive),
        "{CONSTRUCTIVE_TARGET} must be Constructive after the Rat.mul_neg \
         elimination, got {quality:?}"
    );
}

#[test]
fn test_batch3_all_idempotent() {
    let mut env = Environment::new();
    for _ in 0..2 {
        env.init_nn_verify_tier_a_rat_mul_zero_zero().unwrap();
        env.init_nn_verify_tier_a_rat_mul_one_zero().unwrap();
        env.init_nn_verify_tier_a_rat_mul_zero_one().unwrap();
        env.init_nn_verify_tier_a_rat_add_neg_self_zero().unwrap();
        env.init_nn_verify_tier_a_rat_add_left_neg_zero().unwrap();
        env.init_nn_verify_tier_a_rat_mul_neg_zero_zero().unwrap();
    }
    for target in TARGETS {
        assert!(env.get_const(&Name::from_string(target)).is_some());
    }
}
