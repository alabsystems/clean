// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the Tier B `Rat.abs_*` family — Branch B carrier remediation
//! status pins (TCB-shrink Tier 1).
//!
//! # History
//!
//! - #3545 (wave 2) landed four `Rat.abs_*` as `Declaration::Theorem` with
//!   `Eq.refl` / `Rat.le_refl` bodies — but those type-checked only by
//!   δ-collapse of the reducible IDENTITY carrier `Rat.abs = fun a => a`
//!   (#3435), i.e. zero mathematical content (MASQUERADE rules M1+M2+M4).
//! - #3565 (wave 3, Branch A) demoted all four back to honest
//!   `Declaration::Axiom` and co-demoted `Rat.abs` to `Opaque` to close the
//!   δ-reduction attack surface — but the carrier was STILL the identity, so
//!   the axioms remained false-in-model (e.g. `Rat.abs_nonneg : 0 ≤ |a|` reads
//!   `0 ≤ a`, false for `a < 0`), merely non-refutable behind opacity.
//! - TCB-shrink Tier 1 (Branch B, this state) replaced the carrier with the
//!   FAITHFUL reducible Definition `Rat.abs a := Rat.max a (Rat.neg a)` and
//!   PROVED the five tractable lemmas as genuine constructive Theorems over the
//!   sound quotient. The three sign/triangle lemmas (`Rat.abs_mul`,
//!   `Rat.abs_add_le`, `Rat.abs_sub_le`) remain honest admitted axioms pending
//!   the hard batch — but now over the REAL carrier, so they are
//!   non-refutable AND true-in-model (not the old masquerade).
//!
//! These tests pin the current honest state so a future change can't silently
//! regress the carrier back to the identity body or re-introduce a masquerade.

use crate::env::axiom_audit::ProofQuality;
use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::name::Name;

/// All eight `Rat.abs_*` lemmas PROVED as genuine constructive Theorems over
/// the faithful `Rat.max a (Rat.neg a)` carrier (TCB-shrink Tier 1 — five in
/// the easy batch, plus the two triangle inequalities `abs_add_le`/`abs_sub_le`
/// in the hard batch; TCB-shrink Tier 3 — the multiplicative `abs_mul`
/// (`|a·b| = |a|·|b|`) via the four-way sign-case proof in
/// `algebra_rat_abs_mul_proof.rs`).
const PROVEN_THEOREMS: &[&str] = &[
    "Rat.abs_of_nonneg",
    "Rat.abs_of_neg",
    "Rat.abs_zero",
    "Rat.abs_nonneg",
    "Rat.abs_neg",
    "Rat.abs_add_le",
    "Rat.abs_sub_le",
    "Rat.abs_mul",
];

/// No `Rat.abs_*` lemma remains an admitted `Declaration::Axiom`: the last one,
/// `Rat.abs_mul`, was eliminated to a kernel-checked constructive Theorem in
/// TCB-shrink Tier 3 (`algebra_rat_abs_mul_proof.rs`).
const RETAINED_AXIOMS: &[&str] = &[];

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_rat_abs().expect("init_rat_abs should succeed");
    env
}

#[test]
fn test_rat_abs_all_registered() {
    let env = make_env();
    for name in PROVEN_THEOREMS.iter().chain(RETAINED_AXIOMS.iter()) {
        assert!(
            env.get_const(&Name::from_string(name)).is_some(),
            "{name} should be registered"
        );
    }
}

/// `Rat.abs` is now the FAITHFUL reducible Definition `Rat.max a (Rat.neg a)`,
/// NOT the `Opaque` identity carrier. This is the Branch B remediation.
#[test]
fn test_rat_abs_carrier_is_faithful_definition() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string("Rat.abs"))
        .expect("Rat.abs must be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Definition,
        "Rat.abs must be a reducible Definition (= Rat.max a (Rat.neg a)) after \
         the TCB-shrink Tier 1 Branch B carrier remediation; got {:?}",
        info.kind
    );
    assert!(
        info.value.is_some(),
        "Rat.abs must carry the faithful max/neg body"
    );
}

/// Guard: the five proven lemmas MUST be constructive `Declaration::Theorem`s.
/// A regression to `Axiom` here means the Branch B proofs were dropped.
#[test]
fn test_rat_abs_proven_are_constructive_theorems() {
    let env = make_env();
    for name in PROVEN_THEOREMS {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} must be registered"));
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "{name} MUST be a Declaration::Theorem after the TCB-shrink Tier 1 \
             Branch B remediation. Got: {:?}",
            info.kind
        );
        let quality = env
            .proof_quality(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} missing from env"));
        assert_eq!(
            quality,
            ProofQuality::Constructive,
            "{name} must be ProofQuality::Constructive (zero domain-specific \
             axioms in its transitive closure). Got: {quality:?}"
        );
    }
}

/// Guard: NO `Rat.abs_*` lemma remains an admitted `Declaration::Axiom`.
/// `RETAINED_AXIOMS` is empty after the Tier 3 `abs_mul` elimination; any future
/// regression that re-introduces a `Rat.abs_*` axiom (or demotes a proven
/// theorem back to an axiom) must be caught here and in
/// `test_rat_abs_proven_are_constructive_theorems`.
#[test]
fn test_rat_abs_retained_axioms_unchanged() {
    assert!(
        RETAINED_AXIOMS.is_empty(),
        "all Rat.abs_* lemmas are now constructive Theorems; RETAINED_AXIOMS must be empty"
    );
    let env = make_env();
    for name in RETAINED_AXIOMS {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} must be registered"));
        assert_eq!(
            info.kind,
            ConstantKind::Axiom,
            "{name} is expected to remain an Axiom; got {:?}",
            info.kind
        );
        assert!(
            info.value.is_none(),
            "{name} is an Axiom and must not carry a value"
        );
    }
}

#[test]
fn test_rat_abs_init_idempotent() {
    let mut env = Environment::new();
    env.init_rat_abs().unwrap();
    env.init_rat_abs().unwrap();
    assert!(env.has_rat_abs());
    // Spot-check one proven theorem survives a second init call.
    let info = env
        .get_const(&Name::from_string("Rat.abs_zero"))
        .expect("Rat.abs_zero must survive second init_rat_abs");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "Rat.abs_zero must remain a Theorem after idempotent re-init"
    );
}
