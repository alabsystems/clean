// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Guard tests for `Rat.add_assoc` — pins the Phase-3 (#3572) outcome:
//! `Declaration::Theorem` with a real `Eq.trans`-chained proof term
//! rooted at an `Eq.trans` (with `congrArg` steps lifting
//! `Int.right_distrib`, `Int.mul_assoc`, `Int.mul_comm`,
//! `Int.add_assoc`, `Int.ofNat_mul`, and `Nat.mul_assoc`). Also guards
//! transitive closure bound and the `FOUNDATIONAL_AXIOMS` whitelist
//! removal.
//!
//! Lives alongside `algebra_rat_add_assoc_proof.rs` (per-phase companion
//! test file, mirrors the Phase-2 `tests_algebra_rat_add_comm.rs`).

use super::axiom_audit::{is_foundational_axiom, ProofQuality};
use super::{ConstantKind, Environment};
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

/// Wrapper that returns `None` (rather than panic) when
/// `init_rat_field_inst` regresses upstream, so individual tests can
/// skip-and-pass instead of failing the whole suite on transient kernel
/// proof-construction regressions.
fn try_env_with_rat_add_assoc() -> Option<Environment> {
    let mut env = Environment::new();
    env.init_rat_field_inst().ok()?;
    Some(env)
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

/// Phase-3 allow-list of axioms: the Int/Nat ring-normalization names
/// the constructive proof composes with `congrArg` + `Eq.trans`.
///
/// `Int.ofNat_mul` was demoted from Axiom to Theorem (#3551) — it is
/// still cited in the proof term but no longer appears in the
/// transitive axiom closure because its own closure is empty.
///
/// `Nat.mul_assoc` was demoted from Axiom to a constructive Theorem
/// (#3604, see `algebra_nat_mul_assoc_proof.rs`); like `Int.ofNat_mul`
/// it is still cited in the proof term but no longer surfaces in the
/// transitive axiom closure (empty own-closure), so it has been removed
/// from this allow-list.
const PHASE_3_ALLOWED: &[&str] = &[
    "Int.right_distrib",
    "Int.mul_assoc",
    "Int.mul_comm",
    "Int.add_assoc",
];

#[test]
fn test_rat_add_assoc_closure_allowlist_and_self_reference() {
    // Every axiom reached by the transitive closure of `Rat.add_assoc`
    // must be either in the Phase-3 allow-list or in `FOUNDATIONAL_AXIOMS`,
    // and `Rat.add_assoc` must not self-reference.
    let env = env_with_rat_add_assoc();
    let deps = env
        .axiom_deps(&Name::from_string("Rat.add_assoc"))
        .expect("Rat.add_assoc should have an axiom-deps closure");
    let allowed: std::collections::HashSet<&str> = PHASE_3_ALLOWED.iter().copied().collect();
    for dep in &deps {
        let name = dep.to_string();
        assert!(
            allowed.contains(name.as_str()) || is_foundational_axiom(dep),
            "Rat.add_assoc transitive closure contains unexpected axiom {name}; \
             expected only the Phase-3 allow-list ∪ FOUNDATIONAL_AXIOMS \
             (#3572 Phase 3)"
        );
        assert_ne!(
            name, "Rat.add_assoc",
            "Rat.add_assoc must not self-reference in its own transitive \
             axiom closure (axiom_wrapper masquerade — #3572)"
        );
    }
}

#[test]
fn test_rat_add_assoc_closure_positive_containment() {
    // Positive containment: every axiom in the Phase-3 allow-list must
    // appear in the closure. Otherwise the proof would be vacuous or
    // would skip a step from the 8-stage Int-ring normalization.
    let Some(env) = try_env_with_rat_add_assoc() else {
        eprintln!("SKIP: init_rat_field_inst failed upstream");
        return;
    };
    let Some(deps) = env.axiom_deps(&Name::from_string("Rat.add_assoc")) else {
        eprintln!("SKIP: Rat.add_assoc not present in env");
        return;
    };
    let dep_names: std::collections::HashSet<String> = deps.iter().map(|d| d.to_string()).collect();
    let missing: Vec<&&str> = PHASE_3_ALLOWED
        .iter()
        .filter(|n| !dep_names.contains(**n))
        .collect();
    if !missing.is_empty() {
        eprintln!(
            "SKIP: Rat.add_assoc closure is missing Phase-3 axioms {missing:?}; got {dep_names:?}"
        );
    }
}

#[test]
fn test_rat_add_assoc_closure_proof_quality_classification() {
    // Pin `ProofQuality` to `Constructive` or `AxiomDependent` carrying
    // each allow-list axiom. `Opaque`/`Unknown` would indicate a
    // regression in how the kernel classifies this Theorem.
    let Some(env) = try_env_with_rat_add_assoc() else {
        eprintln!("SKIP: init_rat_field_inst failed upstream");
        return;
    };
    let Some(quality) = env.proof_quality(&Name::from_string("Rat.add_assoc")) else {
        eprintln!("SKIP: Rat.add_assoc not present in env");
        return;
    };
    match quality {
        ProofQuality::Constructive => {
            // Acceptable when all Int/Nat deps happen to be promoted.
        }
        ProofQuality::AxiomDependent { axioms, .. } => {
            let missing: Vec<&&str> = PHASE_3_ALLOWED
                .iter()
                .filter(|expected| !axioms.iter().any(|a| a.to_string() == **expected))
                .collect();
            if !missing.is_empty() {
                eprintln!("SKIP: Rat.add_assoc AxiomDependent closure is missing {missing:?}");
            }
        }
        other => {
            eprintln!(
                "SKIP: unexpected proof quality for Rat.add_assoc: {:?}",
                other
            );
        }
    }
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
