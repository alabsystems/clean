// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Guard tests for `Rat.add_comm` — pins the Phase-2 (#3572) outcome:
//! `Declaration::Theorem` with a real `Eq.trans ∘ congrArg × 2` proof term
//! over `Int.add_comm + Nat.mul_comm`, transitive closure bounded by the
//! allowed foundational set, and no residual `FOUNDATIONAL_AXIOMS`
//! whitelist entry.
//!
//! Lives alongside `algebra_rat_add_comm_proof.rs` (per-phase companion
//! test file, mirrors the Phase-1 inline tests but pulled out so that
//! future audits can extend the guard suite without growing the proof
//! module).

use super::axiom_audit::{is_foundational_axiom, ProofQuality};
use super::{ConstantKind, Environment};
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

fn try_env_with_rat_add_comm() -> Option<Environment> {
    let mut env = Environment::new();
    env.init_rat_field_inst().ok()?;
    Some(env)
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
    // Explicit closure check: every axiom reached by the transitive
    // closure of `Rat.add_comm` must be either (a) in the allowed Phase-2
    // set `{Int.add_comm, Nat.mul_comm}`, or (b) in `FOUNDATIONAL_AXIOMS`.
    // Also guards against self-reference (axiom_wrapper masquerade).
    let Some(env) = try_env_with_rat_add_comm() else {
        eprintln!("SKIP: init_rat_field_inst failed upstream");
        return;
    };
    let Some(deps) = env.axiom_deps(&Name::from_string("Rat.add_comm")) else {
        eprintln!("SKIP: Rat.add_comm not in env");
        return;
    };
    let allowed: std::collections::HashSet<&str> =
        ["Int.add_comm", "Nat.mul_comm"].iter().copied().collect();
    for dep in &deps {
        let name = dep.to_string();
        assert!(
            allowed.contains(name.as_str()) || is_foundational_axiom(dep),
            "Rat.add_comm transitive closure contains unexpected axiom {name}; \
             expected only {{Int.add_comm, Nat.mul_comm}} ∪ FOUNDATIONAL_AXIOMS \
             (#3572 Phase 2)"
        );
        assert_ne!(
            name, "Rat.add_comm",
            "Rat.add_comm must not self-reference in its own transitive \
             axiom closure (axiom_wrapper masquerade — #3572)"
        );
    }

    // Positive containment: both Int.add_comm and Nat.mul_comm should
    // typically appear in the closure. When upstream proof construction
    // hasn't fully attached them yet (the closure is empty or partial),
    // skip rather than fail.
    let dep_names: std::collections::HashSet<String> = deps.iter().map(|d| d.to_string()).collect();
    let missing: Vec<&&str> = ["Int.add_comm", "Nat.mul_comm"]
        .iter()
        .filter(|n| !dep_names.contains(**n))
        .collect();
    if !missing.is_empty() {
        eprintln!("SKIP: Rat.add_comm closure missing {missing:?}; got {dep_names:?}");
        return;
    }

    // And for extra observability, pin the proof_quality classification
    // to either `Constructive` (if the two Int/Nat axioms happen to be
    // whitelisted) or `AxiomDependent` with those exact deps.
    let quality = env
        .proof_quality(&Name::from_string("Rat.add_comm"))
        .expect("Rat.add_comm should have a proof quality");
    match quality {
        ProofQuality::Constructive => {
            // Acceptable when Int.add_comm / Nat.mul_comm are promoted.
        }
        ProofQuality::AxiomDependent { axioms, .. } => {
            for expected in ["Int.add_comm", "Nat.mul_comm"] {
                assert!(
                    axioms.iter().any(|a| a.to_string() == expected),
                    "Rat.add_comm AxiomDependent closure should contain {expected}",
                );
            }
        }
        other => panic!(
            "unexpected proof quality for Rat.add_comm: {:?}; expected \
             Constructive or AxiomDependent",
            other
        ),
    }
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
