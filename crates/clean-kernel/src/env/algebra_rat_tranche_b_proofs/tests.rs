// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Guard tests for Rat Tranche B proofs (#3581). See `mod.rs` for the
//! proof bodies and `add_mul.rs` for the four add/mul proof registrations.

#![cfg(test)]

use crate::env::axiom_audit::{is_foundational_axiom, ProofQuality};
use crate::env::{ConstantKind, Environment};
use crate::name::Name;

/// Build an environment with the Rat field instance registered.
fn env_with_rat_field_inst() -> Environment {
    let mut env = Environment::new();
    env.init_rat_field_inst()
        .expect("init_rat_field_inst should succeed");
    env
}

// ------------------------------------------------------------------
// Rat.inv_zero
// ------------------------------------------------------------------

#[test]
fn test_rat_inv_zero_is_theorem_not_axiom() {
    let env = env_with_rat_field_inst();
    let info = env
        .get_const(&Name::from_string("Rat.inv_zero"))
        .expect("Rat.inv_zero should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "Rat.inv_zero should be Declaration::Theorem (post-#3581), got {:?}",
        info.kind
    );
}

#[test]
fn test_rat_inv_zero_proof_quality_is_constructive() {
    let env = env_with_rat_field_inst();
    let quality = env
        .proof_quality(&Name::from_string("Rat.inv_zero"))
        .expect("Rat.inv_zero should have a proof quality");
    assert_eq!(
        quality,
        ProofQuality::Constructive,
        "Rat.inv_zero proof is Eq.refl; transitive axiom closure should \
         be empty (Constructive). Got: {quality:?}"
    );
}

#[test]
fn test_rat_inv_zero_not_in_foundational_axioms() {
    assert!(
        !is_foundational_axiom(&Name::from_string("Rat.inv_zero")),
        "Rat.inv_zero is now a Declaration::Theorem (#3581); it must \
         NOT appear in FOUNDATIONAL_AXIOMS (#3559 disjointness rule)."
    );
}

#[test]
fn test_rat_inv_zero_idempotent() {
    let mut env = Environment::new();
    env.init_rat_field_inst().expect("first init");
    env.init_rat_field_inst().expect("second init (idempotent)");
    env.register_rat_inv_zero_proof()
        .expect("direct re-registration (idempotent)");
    let info = env
        .get_const(&Name::from_string("Rat.inv_zero"))
        .expect("Rat.inv_zero should be registered");
    assert_eq!(info.kind, ConstantKind::Theorem);
}

// ------------------------------------------------------------------
// Rat.zero_add, Rat.add_zero, Rat.one_mul, Rat.mul_one (add_mul.rs)
// ------------------------------------------------------------------

/// Helper: assert a Tranche B name is a Theorem and not in the
/// foundational whitelist.
fn assert_theorem_not_foundational(env: &Environment, name: &str) {
    let info = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} should be registered"));
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "{name} should be Declaration::Theorem (post-#3581), got {:?}",
        info.kind
    );
    assert!(
        !is_foundational_axiom(&Name::from_string(name)),
        "{name} is now a Theorem (#3581); it must NOT appear in \
         FOUNDATIONAL_AXIOMS (#3559 disjointness rule)."
    );
}

#[test]
fn test_rat_zero_add_is_theorem_not_axiom() {
    let env = env_with_rat_field_inst();
    assert_theorem_not_foundational(&env, "Rat.zero_add");
}

#[test]
fn test_rat_add_zero_is_theorem_not_axiom() {
    let env = env_with_rat_field_inst();
    assert_theorem_not_foundational(&env, "Rat.add_zero");
}

#[test]
fn test_rat_one_mul_is_theorem_not_axiom() {
    let env = env_with_rat_field_inst();
    assert_theorem_not_foundational(&env, "Rat.one_mul");
}

#[test]
fn test_rat_mul_one_is_theorem_not_axiom() {
    let env = env_with_rat_field_inst();
    assert_theorem_not_foundational(&env, "Rat.mul_one");
}

/// Each proof should be `AxiomDependent` with Int/Nat primitives in its
/// closure (NOT `Rat.*` self-references — that would be the #3559
/// axiom-wrapper masquerade).
#[test]
fn test_tranche_b_proofs_do_not_self_reference() {
    let env = env_with_rat_field_inst();
    for name in ["Rat.zero_add", "Rat.add_zero", "Rat.one_mul", "Rat.mul_one"] {
        let quality = env
            .proof_quality(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should have a proof quality"));
        match quality {
            ProofQuality::Constructive => {
                // Acceptable: all Int/Nat deps happen to be foundational.
            }
            ProofQuality::AxiomDependent { axioms, .. } => {
                for ax in &axioms {
                    assert_ne!(
                        ax.to_string(),
                        name,
                        "{name} must not self-reference (axiom-wrapper \
                         masquerade, #3559)"
                    );
                    assert!(
                        !ax.to_string().starts_with("Rat."),
                        "{name} transitive closure should not contain \
                         Rat.* axioms, but found {ax}. Expected Int/Nat \
                         primitives only."
                    );
                }
            }
            other => panic!(
                "unexpected proof quality for {name}: {other:?}; expected \
                 Constructive or AxiomDependent"
            ),
        }
    }
}

#[test]
fn test_tranche_b_idempotent() {
    let mut env = Environment::new();
    env.init_rat_field_inst().expect("first init");
    env.init_rat_field_inst().expect("second init");
    env.register_rat_zero_add_proof()
        .expect("zero_add idempotent");
    env.register_rat_add_zero_proof()
        .expect("add_zero idempotent");
    env.register_rat_one_mul_proof()
        .expect("one_mul idempotent");
    env.register_rat_mul_one_proof()
        .expect("mul_one idempotent");
    for name in ["Rat.zero_add", "Rat.add_zero", "Rat.one_mul", "Rat.mul_one"] {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert_eq!(info.kind, ConstantKind::Theorem);
    }
}
