// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the T07 `interval_width_monotone` proof term (#3541).
//!
//! Post #integrity-audit: this proof term is sorry-free and kernel-checked,
//! but it is NOT constructive — it rests on the admitted domain axiom
//! `Rat.le_trans`, so it honestly classifies as `ProofQuality::AxiomDependent`.
//!
//! Paired with
//! `crates/clean-kernel/src/env/nn_verify_interval_arith_width_monotone_proof.rs`
//! (proof-term builder) and the `register_t07_interval_width_monotone` site in
//! `crates/clean-kernel/src/env/nn_verify_interval_arith_proofs.rs`.
//!
//! Guards enforced here:
//! - `NNVerify.IntervalArith.interval_width_monotone` is a
//!   `Declaration::Theorem` carrying a proof term (not `Declaration::Axiom`).
//! - The proof term type-checks under the kernel against the declared
//!   theorem statement.
//! - The proof term is sorry-free (no `sorry` / `sorryAx` anywhere).
//! - The transitive axiom closure contains ONLY admitted domain axioms —
//!   the only non-kernel reference is `Rat.le_trans`, which is an admitted
//!   domain axiom (`ADMITTED_DOMAIN_AXIOMS`), no longer foundational after
//!   the #integrity-audit reclassification.  Therefore `axiom_deps` is
//!   NON-EMPTY (`{Rat.le_trans}`) and the proof honestly classifies as
//!   `ProofQuality::AxiomDependent`, not `Constructive`.
//!
//! Lives in a sibling file (not inline with `nn_verify_interval_arith_proofs.rs`)
//! because that parent file is already well above the 500-line code-quality
//! ceiling and must not grow further.

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

const T07_NAME: &str = "NNVerify.IntervalArith.interval_width_monotone";

/// #3541: T07 `interval_width_monotone` is a genuine `Declaration::Theorem`
/// (not `Declaration::Axiom`) with a proof-term value attached.
#[test]
fn test_t07_interval_width_monotone_is_theorem() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string(T07_NAME))
        .expect("T07 interval_width_monotone should be registered");
    assert_eq!(
        info.kind,
        ConstantKind::Theorem,
        "T07 must be a Theorem after #3541, got {:?}",
        info.kind,
    );
    assert!(
        info.value.is_some(),
        "T07 Theorem must carry a proof term value",
    );
}

/// #3541: the constructive proof term type-checks against the declared
/// theorem statement under the kernel type checker.
#[test]
fn test_t07_interval_width_monotone_type_checks() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string(T07_NAME))
        .expect("T07 should be registered");
    let proof = info
        .value
        .as_ref()
        .expect("T07 theorem should have a proof term");
    let tc = TypeChecker::with_mode(&env, env.mode());
    let inferred = tc
        .infer_type(proof)
        .expect("T07 proof term should type-check");
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "T07 inferred type must match declared theorem type",
    );
}

/// #3541: the proof term is sorry-free (no `sorry` / `sorryAx` references
/// anywhere in the transitive closure).
#[test]
fn test_t07_interval_width_monotone_no_sorry() {
    let env = make_env();
    let info = env
        .get_const(&Name::from_string(T07_NAME))
        .expect("T07 should be registered");
    let sorry = info.sorry_summary();
    assert!(
        !sorry.has_sorry,
        "T07 proof term must be sorry-free (#3541); summary = {sorry:?}",
    );
    let deps = env
        .axiom_deps(&Name::from_string(T07_NAME))
        .expect("axiom_deps should succeed for registered theorem");
    let dep_strs: Vec<String> = deps.iter().map(|d| d.to_string()).collect();
    assert!(
        !dep_strs.iter().any(|d| d == "sorry" || d == "sorryAx"),
        "T07 transitive closure must not reference sorry/sorryAx; got {dep_strs:?}",
    );
}

/// #3541: record the observed domain-axiom closure for auditing.
#[test]
fn test_t07_interval_width_monotone_axiom_deps_recorded() {
    let env = make_env();
    let deps = env
        .axiom_deps(&Name::from_string(T07_NAME))
        .expect("axiom_deps should compute for registered theorem");
    let mut names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
    names.sort();
    eprintln!(
        "[#3541] T07 interval_width_monotone axiom deps ({} axioms): {:?}",
        names.len(),
        names,
    );
    // We record; the closure is now empty (its sole former domain axiom
    // `Rat.le_trans` was eliminated in 7971c3f5) — locked down by
    // `test_t07_interval_width_monotone_constructive_after_le_trans_elim` below.
}

/// #3541 / soundness fix (7971c3f5): the only non-kernel reference in T07's
/// proof term WAS `Rat.le_trans`. That axiom has since been GENUINELY
/// ELIMINATED — it was a FALSE axiom under the free-inductive `Rat` carrier and
/// is now a kernel-checked constructive `Declaration::Theorem` over the
/// effective-denominator `Rat.le` (`algebra_rat_le_trans_proof.rs`). With its
/// sole admitted dependency eliminated, T07's transitive domain-axiom closure is
/// now EMPTY, so T07 honestly classifies as `ProofQuality::Constructive` — a
/// free correctness win flowing from the le_trans elimination, NOT a dishonest
/// foundational-whitelist.
///
/// This test enforces the "Prove" verb discipline from the design doc's Proof
/// Soundness Rules: T07 must be `Constructive` (empty domain-axiom closure, a
/// fortiori no `sorry`/`sorryAx`). If a future edit reintroduces an admitted
/// domain axiom or a `sorry` into the closure, the quality flips to
/// `AxiomDependent` / sorry-reaching and this test fails closed.
#[test]
fn test_t07_interval_width_monotone_constructive_after_le_trans_elim() {
    let env = make_env();
    let quality = env
        .proof_quality(&Name::from_string(T07_NAME))
        .expect("proof_quality should succeed for registered theorem");
    assert!(
        matches!(quality, ProofQuality::Constructive),
        "T07 interval_width_monotone must now be Constructive: its sole admitted \
         dependency `Rat.le_trans` was genuinely eliminated to a kernel-checked \
         Theorem (7971c3f5), emptying its domain-axiom closure. Got {quality:?} \
         — a regression that reintroduced a domain axiom or `sorry` into the \
         closure.",
    );
}
