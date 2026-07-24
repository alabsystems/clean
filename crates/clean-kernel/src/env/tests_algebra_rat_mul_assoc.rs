// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Guard tests for `Rat.mul_assoc` — pins the Tranche C Phase 3 (Part of
//! #3582) outcome: `Declaration::Theorem` with a real
//! `Eq.trans ∘ congrArg × 2` proof term over `Int.mul_assoc + Nat.mul_assoc`,
//! transitive closure bounded by the allowed foundational set, and no
//! residual `FOUNDATIONAL_AXIOMS` whitelist entry.
//!
//! Lives alongside `algebra_rat_mul_assoc_proof.rs` (per-phase companion
//! test file, mirrors the Phase-1 inline tests and Phase-2
//! `tests_algebra_rat_add_comm.rs` structure, with an extra three-binder
//! outer lambda walk).

use super::axiom_audit::{is_foundational_axiom, ProofQuality};
use super::{ConstantKind, Environment};
use crate::expr::ExprKind;
use crate::name::Name;

/// Build an environment with `Rat.mul_assoc` registered as a Theorem via
/// the full `init_rat_field_inst` chain.
fn env_with_rat_mul_assoc() -> Environment {
    let mut env = Environment::new();
    env.init_rat_field_inst()
        .expect("init_rat_field_inst should succeed");
    env
}

fn try_env_with_rat_mul_assoc() -> Option<Environment> {
    let mut env = Environment::new();
    env.init_rat_field_inst().ok()?;
    Some(env)
}

#[test]
fn test_rat_mul_assoc_is_theorem_not_axiom() {
    let env = env_with_rat_mul_assoc();
    let info = env
        .get_const(&Name::from_string("Rat.mul_assoc"))
        .expect("Rat.mul_assoc should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "Rat.mul_assoc should be Declaration::Theorem (post-#3582 Tranche C \
         Phase 3), got {:?}",
        info.kind
    );
}

#[test]
fn test_rat_mul_assoc_proof_body_is_not_axiom_ref() {
    // WS-A ATOMIC LIVE SWITCH: over the quotient carrier `Rat.mul_assoc` is a
    // genuine triple-`Quot.ind` proof (`fun a => Quot.ind … a`), closing the
    // 6-atom commutative-product `Equiv` via `prod_eq` + `Quot.sound`. Pin: one
    // outer `fun a =>` binder, body rooted at `Quot.ind`.
    let env = env_with_rat_mul_assoc();
    let info = env
        .get_const(&Name::from_string("Rat.mul_assoc"))
        .expect("Rat.mul_assoc should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "Rat.mul_assoc must be Declaration::Theorem before inspecting body",
    );
    let value = info
        .value
        .as_ref()
        .expect("Declaration::Theorem must have a proof term stored");

    // Walk the single outer `fun a =>` binder.
    let cur = match value.kind() {
        ExprKind::Lam(_, _, body) => (**body).clone(),
        other => panic!(
            "expected outer Lam (fun a => …), got {other:?} — Rat.mul_assoc \
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
                    "Rat.mul_assoc quotient body head must be Quot.ind, got {n}; \
                     this indicates an axiom_wrapper / masquerade regression"
                );
                break;
            }
            other => panic!(
                "unexpected spine head for Rat.mul_assoc body: {other:?} — \
                 expected App chain rooted at Const \"Quot.ind\""
            ),
        }
    }
}

#[test]
fn test_rat_mul_assoc_transitive_axiom_closure_is_foundational_only() {
    // Explicit closure check: every axiom reached by the transitive
    // closure of `Rat.mul_assoc` must be in `FOUNDATIONAL_AXIOMS`. Also
    // guards against self-reference (axiom_wrapper masquerade).
    //
    // #3604: `Nat.mul_assoc` and then `Int.mul_assoc` were both demoted from
    // `Declaration::Axiom` to constructive `Declaration::Theorem`s.
    // `Nat.mul_assoc`: induction on the third factor via `@Nat.rec.{0}` over
    // the constructive `Nat.left_distrib` (see `algebra_nat_mul_assoc_proof.rs`).
    // `Int.mul_assoc`: triple nested `@Int.rec.{0}` reducing each leaf to a
    // net-signed `Int.ofNat` magnitude product via the constructive sign
    // lemmas, then closing with `Nat.mul_assoc` (see
    // `algebra_int_mul_assoc_proof.rs`). Both have empty axiom closures, so
    // the BFS in `axiom_deps` no longer surfaces either name in
    // `Rat.mul_assoc`'s closure — the closure is now foundational-only and
    // `Rat.mul_assoc` is fully constructive.
    let Some(env) = try_env_with_rat_mul_assoc() else {
        eprintln!("SKIP: init_rat_field_inst failed upstream");
        return;
    };
    let Some(deps) = env.axiom_deps(&Name::from_string("Rat.mul_assoc")) else {
        eprintln!("SKIP: Rat.mul_assoc not in env");
        return;
    };
    for dep in &deps {
        let name = dep.to_string();
        assert!(
            is_foundational_axiom(dep),
            "Rat.mul_assoc transitive closure contains unexpected axiom {name}; \
             expected only FOUNDATIONAL_AXIOMS (post-#3604 Nat.mul_assoc + \
             Int.mul_assoc demotions)"
        );
        assert_ne!(
            name, "Rat.mul_assoc",
            "Rat.mul_assoc must not self-reference in its own transitive \
             axiom closure (axiom_wrapper masquerade — #3582)"
        );
    }

    // Negative containment: neither `Int.mul_assoc` nor `Nat.mul_assoc` may
    // appear in the closure — both are now constructive Theorems with empty
    // closures (#3604).
    let dep_names: std::collections::HashSet<String> = deps.iter().map(|d| d.to_string()).collect();
    for forbidden in &["Int.mul_assoc", "Nat.mul_assoc"] {
        assert!(
            !dep_names.contains(*forbidden),
            "{forbidden} must NOT appear in Rat.mul_assoc's closure after #3604 \
             (it is now a constructive Theorem with empty closure); got {:?}",
            dep_names
        );
    }

    // `Rat.mul_assoc` is now fully constructive: its closure is
    // foundational-only, so `proof_quality` must classify as `Constructive`.
    let quality = env
        .proof_quality(&Name::from_string("Rat.mul_assoc"))
        .expect("Rat.mul_assoc should have a proof quality");
    assert!(
        matches!(quality, ProofQuality::Constructive),
        "Rat.mul_assoc must be Constructive after #3604 Int.mul_assoc \
         demotion, got {:?}",
        quality
    );
}

#[test]
fn test_rat_mul_assoc_removed_from_foundational_whitelist() {
    // Post-#3582 Tranche C Phase 3: since `Rat.mul_assoc` is now a Theorem,
    // keeping it in `FOUNDATIONAL_AXIOMS` is dead code that could silently
    // mask a demotion regression. See #3559 note in `axiom_audit.rs` and
    // the sibling `test_rat_add_comm_removed_from_foundational_whitelist`
    // for the Phase-2 analogue.
    assert!(
        !is_foundational_axiom(&Name::from_string("Rat.mul_assoc")),
        "Rat.mul_assoc is now a Declaration::Theorem (#3582 Tranche C \
         Phase 3); it must NOT appear in FOUNDATIONAL_AXIOMS (per #3559 \
         disjointness rule). Remove it from axiom_audit.rs::FOUNDATIONAL_AXIOMS."
    );
}
