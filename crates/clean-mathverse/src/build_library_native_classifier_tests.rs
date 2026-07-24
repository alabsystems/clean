// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for the `mathverse_shard build-native` axiom classifier —
//! see #3536 / #3554 / #3575.
//!
//! # Background
//!
//! `build_clean_native_library` used to short-circuit every
//! `ConstantKind::Axiom` to `ExcludeReason::NonFoundationalAxiom` without
//! consulting the kernel's `FOUNDATIONAL_AXIOMS` whitelist. This inflated
//! the headline non-foundational-axiom reject count by 10 false positives
//! on the live build (`Classical.choice`, `Classical.em`,
//! `Classical.byContradiction`, `Rat.le_refl`, `Rat.le_trans`,
//! `Rat.le_antisymm`, `Rat.le_total`, `Rat.lt_iff_le_not_le`,
//! `instDecidableEqFin`, `sorryAx`) and made the constructive-shard metric
//! misleading.
//!
//! The fix (#3536) routes the classifier through
//! `clean_kernel::is_foundational_axiom` — the single source of truth for
//! the whitelist — and introduces `ExcludeReason::FoundationalAxiom` plus
//! `CleanNativeBuildResult::foundational_axioms_skipped` so audit consumers
//! can distinguish foundational-axiom skips from trust-gap rejects.
//!
//! # Why this file drives assertions off the canonical API
//!
//! #3554 moved `sorryAx` out of `FOUNDATIONAL_AXIOMS` into the sibling
//! `TRUST_MARKERS` table (a theorem that transitively reaches `sorryAx`
//! must NOT be classified as `Constructive`). A hand-maintained mirror of
//! `FOUNDATIONAL_AXIOMS` in this file previously listed `sorryAx`, so the
//! test broke the moment the canonical table was edited. The drift class is
//! the same one fixed for `sorry_tracer` in #3573. We follow the #3573
//! remediation: drive assertions off the canonical predicates
//! (`is_foundational_axiom` / `is_trust_marker`) at runtime so any future
//! whitelist edit is automatically tracked.
//!
//! # What these tests do
//!
//! - `test_classifier_maps_foundational_axioms_to_foundational_axiom`:
//!   per-name `classify_for_native` branch for the canonical-foundational
//!   subset (filtered by `is_foundational_axiom` at runtime).
//! - `test_classifier_keeps_trust_markers_in_non_foundational`: pins the
//!   post-#3554 contract that trust markers (`sorry`, `sorryAx`,
//!   `trustedArith`, `trustedAy`) classify as `NonFoundationalAxiom`, not
//!   `FoundationalAxiom`.
//! - `test_classifier_keeps_domain_axioms_in_non_foundational`: regression
//!   guard that a domain-specific axiom still classifies as
//!   `NonFoundationalAxiom`.
//! - `test_build_result_counters_split_foundational_from_non_foundational`:
//!   end-to-end headline counters route foundational axioms to
//!   `foundational_axioms_skipped`, trust markers + domain axioms to
//!   `axioms_rejected`.

use clean_kernel::env::is_trust_marker;
use clean_kernel::{is_foundational_axiom, ConstantKind, Declaration, Environment, Name};

use crate::build_library_native::{build_clean_native_library, classify_for_native, ExcludeReason};

/// Representative candidate names spanning every category of the #3554 /
/// #3573 drift classes: pre-#3554 foundational set, the trust markers that
/// MUST classify as non-foundational, and a stable `FOUNDATIONAL_AXIOMS`
/// subset. Each name is partitioned at runtime via `is_foundational_axiom`
/// / `is_trust_marker`, so the test auto-tracks any future edit to the
/// canonical tables.
const CANDIDATE_NAMES: &[&str] = &[
    // Logical core — always foundational.
    "propext",
    "Quot.sound",
    "Classical.choice",
    // NOTE: `Classical.em` and `Classical.byContradiction` are intentionally
    // ABSENT. The DIACONESCU foundational census (−2) retired them from
    // `FOUNDATIONAL_AXIOMS`: they are now kernel-checked `Declaration::Theorem`s
    // (`classical_em_proof.rs` — `em` from `Classical.choice` + `propext` +
    // `funext`, `byContradiction` from `em`), so `is_foundational_axiom` returns
    // false for both and they are not trust markers — i.e. NEITHER. Listing them
    // here as foundational would violate the #3559 disjointness rule and break the
    // `neither.is_empty()` drift check below. Same retirement class as the former
    // `Rat.*` ordering entries (foundational since #3490) and `instDecidableEqFin`,
    // also ABSENT — kernel-checked constructive Theorems over the quotient `Rat`
    // carrier; a computable `Fin` decidable-equality Definition
    // (`algebra_fin_dec_eq_proof.rs`). The `instDecidableEqFin` retirement is pinned
    // by `test_classifier_rejects_retired_instdecidableeqfin_axiom` below.
    // Trust markers — pre-#3554 were foundational; post-#3554 live in
    // `TRUST_MARKERS` and MUST classify as `NonFoundationalAxiom`.
    "sorry",
    "sorryAx",
    "trustedArith",
    "trustedAy",
];

const DOMAIN_AXIOM: &str = "test_domain_specific_axiom_3536";

/// Seed `env` with every name in `CANDIDATE_NAMES` plus `DOMAIN_AXIOM`,
/// all registered as `Declaration::Axiom` over `Prop`.
fn seed_candidates_and_domain_axiom(env: &mut Environment) {
    let prop = clean_kernel::expr::Expr::prop();
    for name in CANDIDATE_NAMES {
        env.add_decl_structural(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: prop.clone(),
        })
        .expect("add candidate axiom");
    }
    env.add_decl_structural(Declaration::Axiom {
        name: Name::from_string(DOMAIN_AXIOM),
        level_params: vec![],
        type_: prop,
    })
    .expect("add domain axiom");
}

/// Partition `CANDIDATE_NAMES` at runtime via the canonical kernel
/// predicates. Returns `(foundational, trust_markers, neither)`.
fn partition_candidates() -> (Vec<&'static str>, Vec<&'static str>, Vec<&'static str>) {
    let mut foundational = Vec::new();
    let mut trust = Vec::new();
    let mut neither = Vec::new();
    for name in CANDIDATE_NAMES {
        let n = Name::from_string(name);
        if is_foundational_axiom(&n) {
            foundational.push(*name);
        } else if is_trust_marker(&n) {
            trust.push(*name);
        } else {
            neither.push(*name);
        }
    }
    (foundational, trust, neither)
}

/// Every name accepted by the canonical `is_foundational_axiom` predicate
/// classifies as `FoundationalAxiom`. Drives assertions off the canonical
/// table so future edits to `FOUNDATIONAL_AXIOMS` do not drift the test.
#[test]
fn test_classifier_maps_foundational_axioms_to_foundational_axiom() {
    let (foundational, _trust, _neither) = partition_candidates();
    assert!(
        !foundational.is_empty(),
        "CANDIDATE_NAMES must include at least one canonical foundational \
         name; accidental wipe of FOUNDATIONAL_AXIOMS would otherwise silently \
         turn this test into a no-op (#3573 / #3575)",
    );

    let mut env = Environment::default();
    seed_candidates_and_domain_axiom(&mut env);
    for name in &foundational {
        let n = Name::from_string(name);
        assert_eq!(
            classify_for_native(&env, &n, ConstantKind::Axiom),
            Some(ExcludeReason::FoundationalAxiom),
            "{name} is on FOUNDATIONAL_AXIOMS (per is_foundational_axiom) — \
             must classify as FoundationalAxiom (#3536)",
        );
    }
}

/// Trust markers (`sorry`, `sorryAx`, `trustedArith`, `trustedAy`) must
/// classify as `NonFoundationalAxiom`, never as `FoundationalAxiom`. Pins
/// the post-#3554 contract that moved `sorryAx` out of the foundational
/// whitelist. Emptiness guard against an accidental wipe of `TRUST_MARKERS`
/// turning the test into a no-op (#3573 / #3575).
#[test]
fn test_classifier_keeps_trust_markers_in_non_foundational() {
    let (_foundational, trust, _neither) = partition_candidates();
    assert!(
        !trust.is_empty(),
        "CANDIDATE_NAMES must include at least one trust marker; accidental \
         wipe of TRUST_MARKERS would otherwise silently turn this test into \
         a no-op (#3554 / #3575)",
    );

    let mut env = Environment::default();
    seed_candidates_and_domain_axiom(&mut env);
    for name in &trust {
        let n = Name::from_string(name);
        assert_eq!(
            classify_for_native(&env, &n, ConstantKind::Axiom),
            Some(ExcludeReason::NonFoundationalAxiom),
            "{name} is a trust marker (per is_trust_marker) — must classify \
             as NonFoundationalAxiom, never FoundationalAxiom (#3554)",
        );
    }
}

/// TCB-shrink retirement pin: `instDecidableEqFin` was REMOVED from
/// `FOUNDATIONAL_AXIOMS` (it is now a computable, axiom-free
/// `Declaration::Definition` — `algebra_fin_dec_eq_proof.rs`). A constant
/// re-declaring the name as an `Axiom` is therefore a plain domain axiom:
/// never foundational, never skipped — rejected as `NonFoundationalAxiom`.
/// Re-whitelisting the name would flip this test (and silently re-grow the
/// TCB).
#[test]
fn test_classifier_rejects_retired_instdecidableeqfin_axiom() {
    let n = Name::from_string("instDecidableEqFin");
    assert!(
        !is_foundational_axiom(&n),
        "instDecidableEqFin must stay retired from FOUNDATIONAL_AXIOMS \
         (TCB-shrink; re-whitelisting a kernel-checked Definition would \
         mask a demotion regression per the #3559 disjointness rule)",
    );
    assert!(
        !is_trust_marker(&n),
        "instDecidableEqFin is not a trust marker"
    );

    let mut env = Environment::default();
    env.add_decl_structural(Declaration::Axiom {
        name: n.clone(),
        level_params: vec![],
        type_: clean_kernel::expr::Expr::prop(),
    })
    .expect("seed retired-name axiom fixture");
    assert_eq!(
        classify_for_native(&env, &n, ConstantKind::Axiom),
        Some(ExcludeReason::NonFoundationalAxiom),
        "an axiom re-declared under the retired name must classify as a \
         plain domain axiom (NonFoundationalAxiom)",
    );
}

/// Domain-specific axioms still classify as `NonFoundationalAxiom`.
#[test]
fn test_classifier_keeps_domain_axioms_in_non_foundational() {
    let mut env = Environment::default();
    seed_candidates_and_domain_axiom(&mut env);
    assert_eq!(
        classify_for_native(&env, &Name::from_string(DOMAIN_AXIOM), ConstantKind::Axiom,),
        Some(ExcludeReason::NonFoundationalAxiom),
        "domain-specific axioms must remain in NonFoundationalAxiom",
    );
}

/// End-to-end: headline counters split foundational axioms from
/// non-foundational (trust markers + domain axioms). Every foundational
/// decision-log entry carries `FoundationalAxiom`; every non-foundational
/// entry carries `NonFoundationalAxiom`. Sets are partitioned at runtime
/// via the canonical predicates, so future edits to the tables auto-track.
#[test]
fn test_build_result_counters_split_foundational_from_non_foundational() {
    let (foundational, trust, neither) = partition_candidates();
    assert!(
        neither.is_empty(),
        "every name in CANDIDATE_NAMES must be either foundational or a \
         trust marker; post-#3554 drift check — unclassified names: {neither:?}",
    );

    let mut env = Environment::default();
    seed_candidates_and_domain_axiom(&mut env);
    let tmp = tempfile::tempdir().expect("tempdir");
    let result = build_clean_native_library(&env, tmp.path()).expect("native build");

    assert_eq!(
        result.foundational_axioms_skipped,
        foundational.len(),
        "every foundational axiom must be counted as skipped, not rejected \
         (canonical set: {foundational:?})",
    );
    // Non-foundational rejected count: trust markers + the one domain axiom.
    assert_eq!(
        result.axioms_rejected,
        trust.len() + 1,
        "axioms_rejected must cover trust markers + domain axiom \
         (trust: {trust:?}, domain: {DOMAIN_AXIOM})",
    );
    for decision in &result.decisions {
        let name = &decision.name;
        if foundational.contains(&name.as_str()) {
            assert_eq!(
                decision.exclude_reason,
                Some(ExcludeReason::FoundationalAxiom),
                "{name} is canonical foundational — must carry \
                 FoundationalAxiom reason",
            );
        } else if trust.contains(&name.as_str()) || name == DOMAIN_AXIOM {
            assert_eq!(
                decision.exclude_reason,
                Some(ExcludeReason::NonFoundationalAxiom),
                "{name} is a trust marker or domain axiom — must carry \
                 NonFoundationalAxiom reason",
            );
        }
    }
}
