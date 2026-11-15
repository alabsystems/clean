// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Guards for the live quotient proof of `Rat.add_assoc`: full kernel
//! validation, a genuine `Quot.ind` body, no domain-specific axioms, and
//! positive evidence that the proof reaches foundational `Quot.sound`.

use super::axiom_audit::{is_foundational_axiom, ProofQuality};
use super::{ConstantKind, DeclarationVerification, Environment};
use crate::expr::ExprKind;
use crate::name::Name;

/// Build an environment with `Rat.add_assoc` registered as a Theorem via
/// the full `init_rat_field_inst` chain.
fn env_with_rat_add_assoc() -> Environment {
    let mut env = Environment::new();
    env.init_rat_field_inst()
        .expect("init_rat_field_inst should succeed");
    env
}

#[test]
fn test_rat_add_assoc_is_theorem_not_axiom() {
    let env = env_with_rat_add_assoc();
    let info = env
        .get_const(&Name::from_string("Rat.add_assoc"))
        .expect("Rat.add_assoc should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "Rat.add_assoc should be Declaration::Theorem (post-#3572 Phase 3), got {:?}",
        info.kind
    );
    assert_eq!(
        env.declaration_verification(&info.name),
        Some(DeclarationVerification::FullKernelCheck),
        "Rat.add_assoc must pass the full kernel gate, not only a structural check",
    );
}

#[test]
fn test_rat_add_assoc_proof_body_is_not_axiom_ref() {
    // WS-A ATOMIC LIVE SWITCH: over the quotient carrier `Rat.add_assoc` is a
    // genuine triple-`Quot.ind` proof (`fun a => Quot.ind … a`), closing the
    // additive cross-`Equiv` by `Quot.sound`. Pin: one outer `fun a =>` binder,
    // body rooted at `Quot.ind`. Guards against an axiom-wrapper masquerade.
    let env = env_with_rat_add_assoc();
    let info = env
        .get_const(&Name::from_string("Rat.add_assoc"))
        .expect("Rat.add_assoc should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "Rat.add_assoc must be Declaration::Theorem before inspecting body",
    );
    let value = info
        .value
        .as_ref()
        .expect("Declaration::Theorem must have a proof term stored");

    // Walk the single outer `fun a =>` binder.
    let cur = match value.kind() {
        ExprKind::Lam(_, _, body) => (**body).clone(),
        other => panic!(
            "expected outer Lam (fun a => …), got {other:?} — Rat.add_assoc \
             quotient body shape regressed (WS-A)"
        ),
    };

    // The body head must be an application whose spine root is `Quot.ind`.
    let mut head = cur;
    loop {
        match head.kind() {
            ExprKind::App(f, _) => head = (**f).clone(),
            ExprKind::Const(n, _) => {
                assert_eq!(
                    n.to_string(),
                    "Quot.ind",
                    "Rat.add_assoc quotient body head must be Quot.ind, got {n}; \
                     this indicates an axiom_wrapper / masquerade regression"
                );
                break;
            }
            other => panic!(
                "unexpected spine head for Rat.add_assoc body: {other:?} — \
                 expected App chain rooted at Const \"Quot.ind\""
            ),
        }
    }
}

#[test]
fn test_rat_add_assoc_closure_allowlist_and_self_reference() {
    // axiom_deps excludes canonical foundational axioms. The live quotient
    // proof must not depend on any of the former Phase-3 domain axioms or
    // self-reference through an axiom wrapper.
    let env = env_with_rat_add_assoc();
    let deps = env
        .axiom_deps(&Name::from_string("Rat.add_assoc"))
        .expect("Rat.add_assoc should have an axiom-deps closure");
    assert!(
        deps.is_empty(),
        "Rat.add_assoc must have no domain-specific or self-referential axiom dependencies: {deps:?}",
    );
}

#[test]
fn test_rat_add_assoc_closure_positive_containment() {
    // The current proof closes representative equality with Quot.sound.
    // Check that positive dependency instead of expecting obsolete Int axioms.
    let env = env_with_rat_add_assoc();
    let deps = env
        .foundational_axiom_deps(&Name::from_string("Rat.add_assoc"))
        .expect("Rat.add_assoc should have a foundational axiom-deps closure");
    assert!(
        deps.contains(&Name::from_string("Quot.sound")),
        "Rat.add_assoc quotient proof must reach Quot.sound; got {deps:?}",
    );
    assert!(deps.iter().all(is_foundational_axiom));
}

#[test]
fn test_rat_add_assoc_closure_proof_quality_classification() {
    // This variant means foundational-axiom-only, not constructive logic.
    let env = env_with_rat_add_assoc();
    assert_eq!(
        env.proof_quality(&Name::from_string("Rat.add_assoc")),
        Some(ProofQuality::Constructive),
        "Rat.add_assoc must be fully proved without domain-specific axioms",
    );
}

#[test]
fn test_rat_add_assoc_removed_from_foundational_whitelist() {
    // Post-#3572 Phase 3: since `Rat.add_assoc` is now a Theorem, keeping
    // it in `FOUNDATIONAL_AXIOMS` is dead code that could silently mask
    // a demotion regression. See #3559 note in `axiom_audit.rs`.
    assert!(
        !is_foundational_axiom(&Name::from_string("Rat.add_assoc")),
        "Rat.add_assoc is now a Declaration::Theorem (#3572 Phase 3); \
         it must NOT appear in FOUNDATIONAL_AXIOMS (per #3559 disjointness \
         rule). Remove it from axiom_audit.rs::FOUNDATIONAL_AXIOMS."
    );
}
