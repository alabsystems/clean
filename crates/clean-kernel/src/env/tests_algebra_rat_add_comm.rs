// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Guards for the live quotient proof of `Rat.add_comm`: full kernel
//! validation, a genuine `Quot.ind` body, no domain-specific axioms, and
//! positive evidence that the proof reaches foundational `Quot.sound`.

use super::axiom_audit::{is_foundational_axiom, ProofQuality};
use super::{ConstantKind, DeclarationVerification, Environment};
use crate::expr::ExprKind;
use crate::name::Name;

/// Build an environment with `Rat.add_comm` registered as a Theorem via
/// the full `init_rat_field_inst` chain.
fn env_with_rat_add_comm() -> Environment {
    let mut env = Environment::new();
    env.init_rat_field_inst()
        .expect("init_rat_field_inst should succeed");
    env
}

#[test]
fn test_rat_add_comm_is_theorem_not_axiom() {
    let env = env_with_rat_add_comm();
    let info = env
        .get_const(&Name::from_string("Rat.add_comm"))
        .expect("Rat.add_comm should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "Rat.add_comm should be Declaration::Theorem (post-#3572 Phase 2), got {:?}",
        info.kind
    );
    assert_eq!(
        env.declaration_verification(&info.name),
        Some(DeclarationVerification::FullKernelCheck),
        "Rat.add_comm must pass the full kernel gate, not only a structural check",
    );
}

#[test]
fn test_rat_add_comm_proof_body_is_not_axiom_ref() {
    // WS-A ATOMIC LIVE SWITCH: over the quotient carrier `Rat.add_comm` is a
    // genuine `Quot.ind` proof (`fun a => Quot.ind … a`), whose per-rep leaf
    // closes the additive cross-`Equiv` by `Quot.sound`. Pin the proof-term
    // shape: one outer `fun a =>` binder, body rooted at `Quot.ind`. Guards
    // against a regression into an axiom-wrapper masquerade.
    let env = env_with_rat_add_comm();
    let info = env
        .get_const(&Name::from_string("Rat.add_comm"))
        .expect("Rat.add_comm should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "Rat.add_comm must be Declaration::Theorem before inspecting body",
    );
    let value = info
        .value
        .as_ref()
        .expect("Declaration::Theorem must have a proof term stored");

    // Walk the single outer `fun a =>` binder.
    let cur = match value.kind() {
        ExprKind::Lam(_, _, body) => (**body).clone(),
        other => panic!(
            "expected outer Lam (fun a => …), got {other:?} — Rat.add_comm \
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
                    "Rat.add_comm quotient body head must be Quot.ind, got {n}; \
                     this indicates an axiom_wrapper / masquerade regression"
                );
                break;
            }
            other => panic!(
                "unexpected spine head for Rat.add_comm body: {other:?} — \
                 expected App chain rooted at Const \"Quot.ind\""
            ),
        }
    }
}

#[test]
fn test_rat_add_comm_transitive_axiom_closure_is_foundational_only() {
    let env = env_with_rat_add_comm();
    let name = Name::from_string("Rat.add_comm");
    let deps = env
        .axiom_deps(&name)
        .expect("Rat.add_comm should have an axiom-deps closure");
    assert!(
        deps.is_empty(),
        "Rat.add_comm must have no domain-specific or self-referential axiom dependencies: {deps:?}",
    );

    // Pin the actual quotient foundation rather than the obsolete Phase-2
    // Int/Nat domain axioms. Missing declarations and initialization failures
    // must fail these guards, not skip their assertions.
    let foundational_deps = env
        .foundational_axiom_deps(&name)
        .expect("Rat.add_comm should have a foundational axiom-deps closure");
    assert!(
        foundational_deps.contains(&Name::from_string("Quot.sound")),
        "Rat.add_comm quotient proof must reach Quot.sound; got {foundational_deps:?}",
    );
    assert!(foundational_deps.iter().all(is_foundational_axiom));
    // This variant means foundational-axiom-only, not constructive logic.
    assert_eq!(
        env.proof_quality(&name),
        Some(ProofQuality::Constructive),
        "Rat.add_comm must be fully proved without domain-specific axioms",
    );
}

#[test]
fn test_rat_add_comm_removed_from_foundational_whitelist() {
    // Post-#3572 Phase 2: since `Rat.add_comm` is now a Theorem, keeping
    // it in `FOUNDATIONAL_AXIOMS` is dead code that could silently mask
    // a demotion regression. See #3559 note in `axiom_audit.rs` and the
    // sibling `test_rat_mul_comm_not_in_foundational_axioms` for the
    // Phase-1 analogue.
    assert!(
        !is_foundational_axiom(&Name::from_string("Rat.add_comm")),
        "Rat.add_comm is now a Declaration::Theorem (#3572 Phase 2); \
         it must NOT appear in FOUNDATIONAL_AXIOMS (per #3559 disjointness \
         rule). Remove it from axiom_audit.rs::FOUNDATIONAL_AXIOMS."
    );
}
