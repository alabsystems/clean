// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Transitive-axiom-closure honesty guard for the clean-verify spec (M2).
//!
//! Two fail-closed tests, both computed BY KERNEL GROUND TRUTH
//! ([`clean_kernel::Environment::axiom_deps`] over the live spec env), not from
//! the hand-maintained `proof_status` / `axiom_deps` honesty fields:
//!
//!  1. [`no_spec_closure_reaches_a_forbidden_trust_marker`] — CRITICAL, NO
//!     ALLOWLIST. No `SpecDefinition`'s transitive closure may reach
//!     `sorry` / `sorryAx` / `trustedArith` / `trustedAy`. Currently 0; must stay
//!     0. A sound checker would never certify a proof resting on one.
//!
//!  2. [`derivedproved_debt_overclaim_subset_of_golden`] — every `DerivedProved`
//!     def whose TRUE non-foundational closure (DEBT) is non-empty must be in the
//!     checked-in golden `data/clean_verify_derivedproved_debt.json`. SUBSET
//!     semantics: proving a leaf away DRAINS an entry and still passes; a NEW
//!     overclaiming def FAILS closed and cannot silently grow the pinned set.
//!
//! See `crates/clean-verify/src/spec_axiom_closure.rs` for the base definition.

use std::collections::{BTreeMap, BTreeSet};

use clean_verify::spec::ProofStatus;
use clean_verify::spec_axiom_closure::{
    computed_axiom_closure, computed_trust_markers, foundational_base, partition_closure,
};
use clean_verify::test_utils::build_spec_with_stack;

/// The checked-in golden, embedded in the test binary (mirrors
/// `tests/axiom_ratchet.rs`).
const GOLDEN_JSON: &str = include_str!("../../../data/clean_verify_derivedproved_debt.json");

#[derive(serde::Deserialize)]
struct Golden {
    count: usize,
    /// def name -> sorted list of its DEBT axiom names.
    entries: BTreeMap<String, Vec<String>>,
}

fn load_golden() -> Golden {
    serde_json::from_str(GOLDEN_JSON).expect(
        "data/clean_verify_derivedproved_debt.json must be valid JSON for the debt-overclaim schema",
    )
}

/// (1) CRITICAL fail-closed, NO ALLOWLIST: no spec definition's transitive
/// closure may reach a forbidden trust marker. Computed by kernel ground truth.
#[test]
fn no_spec_closure_reaches_a_forbidden_trust_marker() {
    let spec = build_spec_with_stack();

    let mut hits: Vec<String> = Vec::new();
    for def in spec.definitions().values() {
        let markers = computed_trust_markers(&spec, &def.name);
        if !markers.is_empty() {
            let mut m: Vec<String> = markers.into_iter().collect();
            m.sort();
            hits.push(format!("{} -> {:?}", def.name, m));
        }
    }
    hits.sort();

    assert!(
        hits.is_empty(),
        "CRITICAL TRUST-MARKER REACH: {} spec definition(s) transitively reach a forbidden \
         trust marker (sorry / sorryAx / trustedArith / trustedAy):\n  {}\n\n\
         A spec proof must NEVER rest on an incomplete-proof sentinel or an unverified \
         decision-procedure bridge. There is NO allowlist for this — it is fail-closed. The \
         offending proof term must be repaired so its kernel-ground-truth closure \
         (Environment::axiom_deps) contains no trust marker.",
        hits.len(),
        hits.join("\n  ")
    );
}

/// (2) DEBT-overclaim ratchet: the set of `DerivedProved` defs whose TRUE
/// non-foundational closure is non-empty must be a SUBSET of the golden.
#[test]
fn derivedproved_debt_overclaim_subset_of_golden() {
    let golden = load_golden();
    assert_eq!(
        golden.entries.len(),
        golden.count,
        "data/clean_verify_derivedproved_debt.json: `count` ({}) must equal the number of \
         distinct golden entries ({})",
        golden.count,
        golden.entries.len()
    );

    let spec = build_spec_with_stack();
    let base = foundational_base(&spec);

    // Live: every DerivedProved def -> its DEBT closure (closure − base − markers).
    let mut live_debt: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for def in spec.definitions().values() {
        if def.proof_status != ProofStatus::DerivedProved {
            continue;
        }
        let closure = computed_axiom_closure(&spec, &def.name);
        let (_markers, debt) = partition_closure(&closure, &base);
        if !debt.is_empty() {
            live_debt.insert(def.name.clone(), debt);
        }
    }

    let golden_keys: BTreeSet<&String> = golden.entries.keys().collect();

    // SUBSET semantics: a live DerivedProved-with-DEBT def absent from the golden
    // is a NEW overclaim — fail closed. (A drained golden entry simply has no live
    // counterpart; that still passes.)
    let mut new_overclaims: Vec<String> = Vec::new();
    for (name, debt) in &live_debt {
        if !golden_keys.contains(name) {
            let mut d: Vec<&String> = debt.iter().collect();
            d.sort();
            new_overclaims.push(format!("{name} -> {d:?}"));
        }
    }
    new_overclaims.sort();

    assert!(
        new_overclaims.is_empty(),
        "DERIVEDPROVED DEBT-OVERCLAIM: {} def(s) are labeled DerivedProved but their TRUE \
         transitive non-foundational closure (computed by Environment::axiom_deps over the live \
         spec env, MINUS the foundational base, MINUS trust markers) is NON-EMPTY and they are \
         NOT in the golden data/clean_verify_derivedproved_debt.json:\n  {}\n\n\
         The DerivedProved label claims the closure rests only on the foundational base — a new \
         non-empty residual is a masquerade-shaped overclaim. EITHER:\n  \
         (1) PROVE the offending leaf away (discharge the pending track / give it a real value) \
         so the residual drains — the live set shrinks, stays a subset, still passes; OR\n  \
         (2) if this DerivedProved-with-debt is genuinely intended, ADD it (name + its debt \
         axioms) to data/clean_verify_derivedproved_debt.json (bump `count`) with a review \
         justification, so the addition is a visible, reviewable diff.",
        new_overclaims.len(),
        new_overclaims.join("\n  ")
    );

    // Guard the golden itself: it must not carry an entry that is no longer a live
    // DerivedProved-with-debt def under the SAME debt axioms (a stale entry could
    // mask a future re-introduction under that name). A drain that REMOVES the def
    // from the live set is fine — but if the def is still live and DerivedProved
    // yet its recorded debt no longer matches, the golden is out of date.
    let mut stale: Vec<String> = Vec::new();
    for (name, golden_debt) in &golden.entries {
        match live_debt.get(name) {
            // Fully drained (no longer live debt) — legitimate, skip.
            None => {}
            Some(actual) => {
                let recorded: BTreeSet<String> = golden_debt.iter().cloned().collect();
                if &recorded != actual {
                    let mut a: Vec<&String> = actual.iter().collect();
                    a.sort();
                    stale.push(format!("{name}: golden {golden_debt:?} != live {a:?}"));
                }
            }
        }
    }
    stale.sort();
    assert!(
        stale.is_empty(),
        "STALE GOLDEN: {} golden entry(ies) record DEBT axioms that diverge from the live \
         kernel-ground-truth closure (the proof changed without updating the pin):\n  {}\n\n\
         Update data/clean_verify_derivedproved_debt.json to the def's true current debt axioms \
         (or drain it by proving the leaves away).",
        stale.len(),
        stale.join("\n  ")
    );
}
