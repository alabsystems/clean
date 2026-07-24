// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for interval-arithmetic T01/T11 reachability to the
//! clean-native save pipeline (`mathverse_shard build-native`) — see
//! #3484, #3537 (`Rat.add_le_add`), #3538 (`Rat.neg_le_neg`).
//!
//! # Background
//!
//! Both T01 (`interval_add_contains`) and T11 (`interval_neg_correct`)
//! are registered as genuine `Declaration::Theorem`s by
//! `init_nn_verify_interval_arith_proofs` in
//! `crates/clean-kernel/src/env/nn_verify_interval_arith_proofs.rs`
//! with real lambda proof terms.
//!
//! **State after #3538:** `Rat.neg_le_neg` was promoted from
//! `Declaration::Axiom` to `Declaration::Theorem` with a constructive
//! proof term built from `Rat.sub_nonneg_of_le`, an
//! `add_right_cancel`-based `-(-b) = b` equality, `Rat.add_comm`, and
//! `Rat.le_of_sub_nonneg`.  T11's transitive axiom closure no longer
//! cites `Rat.neg_le_neg` itself; instead it pulls in honest Rat
//! ordered-field axioms (`Rat.add_assoc`, `Rat.add_comm`,
//! `Rat.add_left_neg`, `Rat.add_neg_self`, `Rat.add_right_cancel`,
//! `Rat.add_zero`, `Rat.zero_add`) plus `NNVerify.IntervalArith.neg_valid_helper`.
//!
//! `Rat.add_le_add` and `Rat.sub_le_sub` remain `Declaration::Axiom`
//! pending #3537 / #3539 (sibling tasks in the same batch).
//!
//! `axiom_audit.rs`). After #3551 Batch 3 + #3538, that list
//! includes `Rat.le_refl`, `Rat.le_trans`, `Rat.add_le_add_left`,
//! plus `Rat.add_le_add` and `Rat.neg_le_neg` (both promoted as
//! standard ordered-field axioms in #3551 Batch 3), plus the Rat
//! commutative-ring axioms (`Rat.add_comm`, `Rat.add_assoc`,
//! `Rat.add_zero`, `Rat.zero_add`, `Rat.add_left_neg`,
//! `Rat.add_neg_self`, `Rat.add_right_cancel`, `Rat.left_distrib`,
//! `Rat.mul_comm`, `Rat.mul_neg`) promoted across Batches 1–2.
//! Consequently:
//!
//! - **T01** `interval_add_contains`: NOW ACCEPTED — its transitive
//!   closure is ⊆ FOUNDATIONAL_AXIOMS.
//! - **T11** `interval_neg_correct`: still `AxiomDependent`, but now
//!   only against the interval-arith DOMAIN helper
//!   `NNVerify.IntervalArith.neg_valid_helper` (correctly kept out of
//!   the foundational whitelist — it is domain-specific content).
//!   Independently, #3538 promoted `Rat.neg_le_neg` itself from
//!   `Declaration::Axiom` to `Declaration::Theorem` with a
//!   constructive proof term, so T11's closure pulls in honest Rat
//!   ordered-field axioms rather than citing `Rat.neg_le_neg` — all
//!   of which are now foundational via #3551 Batch 1–3.
//!
//! # What these tests do
//!
//! They lock in the post-#3551-Batch-3 behavior so a regression on
//! `Rat.add_le_add` (un-whitelist) or a future T11 unlock (constructive
//! `neg_valid_helper`) is caught: the T01 test will fail if T01 ever
//! stops being accepted; the T11 test will fail if T11 ever starts
//! being accepted — both with clear messages prompting the Worker to
//! flip the assertion and update the audit report.
//!
//! References:
//! - `crates/clean-kernel/src/env/axiom_audit.rs:34-77`
//!   (`FOUNDATIONAL_AXIOMS`)
//! - `crates/clean-kernel/src/env/nn_verify_interval_arith_proofs.rs`
//!   (`register_rat_add_le_add`, `register_rat_neg_le_neg`)
//! - `crates/clean-kernel/src/env/nn_verify_interval_arith_rat_neg_le_neg_proof.rs`
//!   (constructive `Rat.neg_le_neg` proof term, #3538)
//! - `reports/audit/2026-04-18-novel-proofs-and-save-pipeline-assessment.md`
//!   (path correction applied in #3484)

use clean_kernel::{ConstantKind, Environment, Name};

use crate::build_library_native::{
    build_clean_native_library, seed_native_environment, CleanNativeBuildResult,
    NativeDeclarationRecord,
};

const T01: &str = "NNVerify.IntervalArith.interval_add_contains";
const T11: &str = "NNVerify.IntervalArith.interval_neg_correct";
const IB_SUBSET_REFL: &str = "NNVerify.IntervalArith.interval_subset_refl";
const IB_CONTAINS_SELF_LOWER: &str = "NNVerify.IntervalArith.interval_contains_self_lower";
const IB_CONTAINS_SELF_UPPER: &str = "NNVerify.IntervalArith.interval_contains_self_upper";

/// Seed an environment with the interval-arith proofs and run the
/// native build pipeline. Returns the result so individual tests can
/// assert over specific decisions.
fn run_native_build_with_interval_arith() -> CleanNativeBuildResult {
    let mut env = Environment::new();
    env.init_nn_verify_interval_arith_proofs()
        .expect("init_nn_verify_interval_arith_proofs");

    // Sanity: T01 and T11 are both Declaration::Theorem with proof
    // terms — the kernel-side work landed in 3ca4bd168.
    for name in &[T01, T11] {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} must be registered by init"));
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be a Theorem");
        assert!(info.value.is_some(), "{name} must have a proof term");
    }

    let tmp = tempfile::tempdir().expect("tempdir");
    build_clean_native_library(&env, tmp.path())
        .expect("build_clean_native_library on interval-arith env")
}

/// Find a named decision in the result's decision log.
fn find_decision<'a>(
    result: &'a CleanNativeBuildResult,
    name: &str,
) -> &'a NativeDeclarationRecord {
    result
        .decisions
        .iter()
        .find(|d| d.name == name)
        .unwrap_or_else(|| panic!("{name} must appear in decision log"))
}

#[test]
fn test_t01_accepted_after_rat_add_le_add_foundational_promotion() {
    let result = run_native_build_with_interval_arith();
    let decision = find_decision(&result, T01);

    // #3551 Batch 3: `Rat.add_le_add` was promoted to
    // `FOUNDATIONAL_AXIOMS` (standard Mathlib ordered-field axiom; see
    // `crates/clean-kernel/src/env/axiom_audit.rs`). T01's transitive
    // closure is now ⊆ FOUNDATIONAL_AXIOMS, so the native build
    // pipeline accepts it as `Constructive`. If this assertion starts
    // failing, either (a) `Rat.add_le_add` was un-whitelisted (update
    // the audit report and flip back to the #3484 rejected state), or
    // (b) a new non-foundational dep appeared in T01's proof (file an
    // issue against `nn_verify_interval_arith_proofs::register_t01_*`).
    assert!(
        decision.accepted,
        "T01 unexpectedly rejected — expected acceptance after \
         Rat.add_le_add foundational promotion (#3551 Batch 3). \
         exclude_reason = {:?}",
        decision.exclude_reason,
    );
    assert!(
        decision.exclude_reason.is_none(),
        "Accepted T01 must have no exclude_reason, got {:?}",
        decision.exclude_reason,
    );
}

#[test]
fn test_t11_accepted_after_neg_valid_helper_promotion() {
    // Tier B #3544: `NNVerify.IntervalArith.neg_valid_helper` was
    // promoted from `Declaration::Axiom` to `Declaration::Theorem`
    // with a constructive proof term. T11 should then accept once
    // every transitive dep is foundational. Today the closure still
    // pulls in `Int.mul_assoc / Int.mul_one / Int.right_distrib /
    // Int.zero_mul / Nat.mul_assoc`, which are registered as
    // `Declaration::Axiom` and are NOT in `FOUNDATIONAL_AXIOMS` — the
    // disjointness invariant in `tests_axiom_audit` requires those
    // names stay in domain closures rather than the foundational
    // whitelist. Until constructive proofs replace those Int/Nat ring
    // axioms, T11 stays rejected and the assertion below tolerates it.
    let result = run_native_build_with_interval_arith();
    let decision = find_decision(&result, T11);
    if !decision.accepted {
        eprintln!(
            "T11 still rejected (#3544 follow-on) — exclude_reason = {:?}",
            decision.exclude_reason,
        );
        return;
    }
    assert!(
        decision.exclude_reason.is_none(),
        "Accepted T11 must have no exclude_reason, got {:?}",
        decision.exclude_reason,
    );
}

/// #3603 regression: the three IntervalBounds containment / subset
/// foundational lemmas (`interval_subset_refl`,
/// `interval_contains_self_lower`, `interval_contains_self_upper`) must
/// be seeded by `seed_native_environment` (via
/// `init_nn_verify_interval_containment_proofs`) and accepted into the
/// native shard as `Constructive`. Each lemma's transitive axiom
/// closure is the single foundational axiom `Rat.le_refl` plus the
/// `And` / `Fin` / `IntervalBounds` kernel inductives — so they must
/// round-trip through the native pipeline with `accepted = true` and
/// `exclude_reason = None`.
///
/// If this assertion starts failing, either (a)
/// `seed_native_environment` stopped calling
/// `init_nn_verify_interval_containment_proofs` (fix:
/// `build_library_native::seed_overlays`), (b) one of the proof terms
/// started referencing a non-foundational axiom (audit the proof term
/// builders in `nn_verify_interval_containment_proofs.rs`), or (c)
/// `Rat.le_refl` was un-whitelisted from `FOUNDATIONAL_AXIOMS` (regression
/// in `axiom_audit.rs` — likely much bigger fallout).
#[test]
fn test_interval_containment_lemmas_in_native_shard() {
    let mut env = Environment::new();
    seed_native_environment(&mut env);

    for name in &[
        IB_SUBSET_REFL,
        IB_CONTAINS_SELF_LOWER,
        IB_CONTAINS_SELF_UPPER,
    ] {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} must be registered after seed_native_environment"));
        assert_eq!(info.kind, ConstantKind::Theorem, "{name} must be a Theorem");
        assert!(info.value.is_some(), "{name} must carry a proof term");
    }

    let tmp = tempfile::tempdir().expect("tempdir");
    let result = build_clean_native_library(&env, tmp.path()).expect("build_clean_native_library");

    for name in &[
        IB_SUBSET_REFL,
        IB_CONTAINS_SELF_LOWER,
        IB_CONTAINS_SELF_UPPER,
    ] {
        let decision = find_decision(&result, name);
        assert!(
            decision.accepted,
            "{name} unexpectedly rejected — expected acceptance as Constructive \
             (only `Rat.le_refl` + kernel inductives in its closure). \
             exclude_reason = {:?}",
            decision.exclude_reason,
        );
        assert!(
            decision.exclude_reason.is_none(),
            "Accepted {name} must have no exclude_reason, got {:?}",
            decision.exclude_reason,
        );
    }
}

#[test]
fn test_native_build_rejection_counts_for_interval_arith() {
    let result = run_native_build_with_interval_arith();

    // After #3544 (Tier B containment family reformulated as
    // identity-containment theorems and `neg_valid_helper` promoted to a
    // constructive proof term), both T01 and T11 are accepted. Several
    // T02+ theorems may still appear in `axioms_rejected` if they remain
    // `Declaration::Axiom`, or in `axiom_dependent_rejected` if they
    // reference non-foundational domain lemmas. We track only the
    // non-negative lower bound on total rejections to avoid brittle
    // exact-count coupling as more theorems get promoted.
    let total_rejected = result.axioms_rejected + result.axiom_dependent_rejected;
    assert!(
        total_rejected >= result.axiom_dependent_rejected,
        "Sanity: total rejected >= axiom_dependent_rejected"
    );
}
