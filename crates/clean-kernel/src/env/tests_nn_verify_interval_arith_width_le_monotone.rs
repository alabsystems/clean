// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the interval *width* monotonicity lemma
//! `NNVerify.IntervalArith.interval_width_le_monotone`.
//!
//! This is the genuine numeric width-narrowing statement
//! (`subset B1 B2 → ∀ i, width B1 i ≤ width B2 i`), distinct from the
//! historically-named `interval_width_monotone` which proves *containment*
//! monotonicity.
//!
//! Paired with
//! `crates/clean-kernel/src/env/nn_verify_interval_arith_width_le_monotone_proof.rs`
//! (proof-term builder) and the `register_t07b_interval_width_le_monotone`
//! site in
//! `crates/clean-kernel/src/env/nn_verify_interval_arith_proofs.rs`.
//!
//! Guards enforced here:
//! - The lemma is a `Declaration::Theorem` carrying a proof term (not an
//!   `Declaration::Axiom` — i.e. not a masquerade).
//! - The proof term type-checks under the kernel against the declared
//!   theorem statement.
//! - The proof term is sorry-free (no `sorry` / `sorryAx` anywhere).
//! - The transitive domain-axiom closure is EMPTY — the only non-kernel
//!   reference is `Rat.sub_le_sub`, itself a kernel-checked constructive
//!   `Declaration::Theorem` with empty domain-axiom closure. Hence the lemma
//!   classifies as `ProofQuality::Constructive`.

use crate::env::axiom_audit::ProofQuality;
use crate::env::types::ConstantKind;
use crate::env::Environment;
use crate::name::Name;
use crate::tc::TypeChecker;

fn make_env() -> Environment {
    let mut env = Environment::new();
    env.init_nn_verify_interval_arith_proofs()
        .expect("init_nn_verify_interval_arith_proofs");
    env
}

const NAME: &str = "NNVerify.IntervalArith.interval_width_le_monotone";

/// The width-monotonicity lemma is a genuine `Declaration::Theorem` with a
/// proof-term value attached (not a `Declaration::Axiom` masquerade).
#[test]
fn test_interval_width_le_monotone_is_theorem() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string(NAME))
        .expect("interval_width_le_monotone should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "width-monotonicity must be a Theorem, got {:?}",
        info.kind,
    );
    assert!(
        info.value.is_some(),
        "width-monotonicity Theorem must carry a proof-term value",
    );
}

/// The proof term type-checks against the declared theorem statement under
/// the kernel type checker.
#[test]
fn test_interval_width_le_monotone_type_checks() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string(NAME))
        .expect("interval_width_le_monotone should be registered");
    let proof = info
        .value
        .as_ref()
        .expect("theorem should have a proof term");
    let tc = TypeChecker::with_mode(&env, env.mode());
    let inferred = tc
        .infer_type(proof)
        .expect("width-monotonicity proof term should type-check");
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "inferred type must match the declared theorem type",
    );
}

/// The proof term is sorry-free (no `sorry` / `sorryAx` references anywhere in
/// the transitive closure).
#[test]
fn test_interval_width_le_monotone_no_sorry() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string(NAME))
        .expect("interval_width_le_monotone should be registered");
    let sorry = info.sorry_summary();
    assert!(
        !sorry.has_sorry,
        "width-monotonicity proof term must be sorry-free; summary = {sorry:?}",
    );
    let deps = env
        .axiom_deps(&Name::from_string(NAME))
        .expect("axiom_deps should succeed for registered theorem");
    let dep_strs: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
    assert!(
        !dep_strs.iter().any(|d| d == "sorry" || d == "sorryAx"),
        "transitive closure must not reference sorry/sorryAx; got {dep_strs:?}",
    );
}

/// The transitive domain-axiom closure is EMPTY — the sole non-kernel
/// reference is `Rat.sub_le_sub`, a kernel-checked constructive Theorem with
/// empty domain-axiom closure. The lemma therefore honestly classifies as
/// `ProofQuality::Constructive` (the "prove" verb discipline). If a future
/// edit reintroduces an admitted domain axiom or a `sorry` into the closure,
/// the quality flips and this test fails closed.
#[test]
fn test_interval_width_le_monotone_is_constructive() {
    let env = make_env();
    let deps = env
        .axiom_deps(&Name::from_string(NAME))
        .expect("axiom_deps should compute for registered theorem");
    let mut names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
    names.sort();
    eprintln!(
        "[width_le_monotone] domain-axiom closure ({} axioms): {names:?}",
        names.len(),
    );
    let quality = env
        .proof_quality(&Name::from_string(NAME))
        .expect("proof_quality should succeed for registered theorem");
    assert!(
        matches!(quality, ProofQuality::Constructive),
        "interval_width_le_monotone must be Constructive (empty domain-axiom \
         closure): its sole dependency `Rat.sub_le_sub` is a kernel-checked \
         constructive Theorem. Got {quality:?} with closure {names:?} — a \
         regression that admitted a domain axiom or reached `sorry`.",
    );
}
