// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! No-new-axioms ratchet test for the clean-verify self-verification spec.
//!
//! This is the spec-side analogue of the kernel's `golden_matches_live_axioms`
//! (`data/soundness_tcb.json`): it pins the FULL set of admitted-axiom names
//! against the checked-in golden `data/clean_verify_axiom_ratchet.json` and
//! fails closed if a NEW admitted axiom appears.
//!
//! ## Census by kernel GROUND TRUTH (not the `is_axiom` flag)
//!
//! The census walks the kernel ENVIRONMENT for every constant the kernel holds
//! as [`clean_kernel::ConstantKind::Axiom`] (value-less, taken on faith), via
//! [`clean_verify::axiom_ratchet::live_env_axioms`]. It does NOT key on the
//! `SpecDefinition::is_axiom` flag, because the kernel admits ANY value-less
//! declaration as a real `Declaration::Axiom` regardless of that flag
//! (`prepare_definition_decl` keys SOLELY on value-absence). Keying on the
//! kernel's `ConstantKind::Axiom` closes two holes the old flag-based census
//! never saw:
//!   - C1: a `{is_axiom:false, value_src:None}` def lowering to a genuine kernel
//!     axiom (`PendingLeaf`); and
//!   - M1: an axiom injected into the env with no `SpecDefinition` at all
//!     (`EnvInjected` — e.g. the kernel's `propext` / `Quot.sound` /
//!     `Classical.choice` bedrock, the `Quot` primitives, trust markers).
//!
//! ## Semantics (SUBSET, not equality)
//!
//! - A NEW admitted axiom (a live kernel-env axiom name absent from the golden)
//!   FAILS this test. Admitting an axiom is thereby an EXPLICIT, REVIEWED act.
//! - A DRAIN (proving an axiom away so its kernel constant gains a value and is
//!   no longer `ConstantKind::Axiom`, or removing it) keeps the live set a
//!   subset of the golden, so the test still PASSES — the ongoing drain is never
//!   blocked.
//!
//! See `clean_verify::axiom_ratchet` for the reusable check and its fail-closed
//! unit tests.

use std::collections::BTreeSet;

use clean_verify::axiom_ratchet::{live_env_axioms, newly_admitted_axioms, origin_label};
use clean_verify::test_utils::build_spec_with_stack;

/// The checked-in golden, embedded in the test binary (mirrors the kernel's
/// `include_str!("../../../../data/soundness_tcb.json")`).
const GOLDEN_JSON: &str = include_str!("../../../data/clean_verify_axiom_ratchet.json");

#[derive(serde::Deserialize)]
struct GoldenAxiom {
    name: String,
}

#[derive(serde::Deserialize)]
struct Golden {
    count: usize,
    axioms: Vec<GoldenAxiom>,
    #[serde(rename = "_trust_breakdown")]
    trust_breakdown: TrustBreakdown,
}

/// The 3/4/4 partition that backs the headline "genuine axiomatic trust = 3".
/// Until this was deserialized and asserted, the split existed only as JSON
/// prose: nothing stopped a census entry from being uncategorized, from
/// appearing in two buckets, or from the headline count drifting off its own
/// list.
#[derive(serde::Deserialize)]
struct TrustBreakdown {
    genuine_foundational_axioms: Vec<String>,
    genuine_foundational_axiom_count: usize,
    quotient_primitives_not_axioms: Vec<String>,
    honesty_tripwires_anti_trust: Vec<String>,
}

fn load_golden() -> Golden {
    serde_json::from_str(GOLDEN_JSON)
        .expect("data/clean_verify_axiom_ratchet.json must be valid JSON for the ratchet schema")
}

/// THE RATCHET: every live kernel-env axiom name must already be in the golden.
/// A new admission fails closed; a drain (live ⊂ golden) passes.
#[test]
fn no_new_admitted_axioms_in_spec() {
    let golden = load_golden();
    let golden_names: BTreeSet<String> = golden.axioms.iter().map(|a| a.name.clone()).collect();
    assert_eq!(
        golden_names.len(),
        golden.count,
        "data/clean_verify_axiom_ratchet.json: `count` ({}) must equal the number of \
         distinct axiom names ({})",
        golden.count,
        golden_names.len()
    );

    let spec = build_spec_with_stack();
    let live = live_env_axioms(&spec);
    let live_names: Vec<String> = live.iter().map(|a| a.name.clone()).collect();

    let new_names = newly_admitted_axioms(&live_names, &golden_names);
    assert!(
        new_names.is_empty(),
        "NO-NEW-AXIOMS RATCHET VIOLATION: {} kernel-env axiom name(s) are LIVE in the \
         clean-verify spec (the kernel holds them as ConstantKind::Axiom — value-less, \
         taken on faith) but absent from the golden \
         data/clean_verify_axiom_ratchet.json:\n  {}\n\n\
         An axiom is an ASSUMPTION the kernel does not check for truth (the kind of \
         thing that let two FALSE micro_whnf axioms hide for a long time). This census \
         keys on the kernel ConstantKind::Axiom (value-absence), NOT the SpecDefinition \
         is_axiom flag — so even a {{is_axiom:false, value_src:None}} def that lowers to a \
         genuine kernel axiom is caught here. Adding one must be an explicit, reviewed \
         act. EITHER:\n  \
         (1) PROVE it instead — give the SpecDefinition a real value so its kernel \
         constant lowers to Theorem/Opaque (no longer ConstantKind::Axiom); OR\n  \
         (2) if a new axiom is genuinely intended, ADD each name to \
         data/clean_verify_axiom_ratchet.json (bump `count`) with a justification, so \
         the addition shows up as a visible, reviewable diff.",
        new_names.len(),
        new_names.join("\n  ")
    );
}

/// THE 3/4/4 PARTITION, code-enforced.
///
/// The census headline is "genuine axiomatic trust = 3"; the other 8 entries are
/// the 4 `Quot` type-formers (CIC primitives, which Lean's `#print axioms` never
/// lists) and the 4 anti-trust tripwires the closure-honesty gate proves
/// unreachable. That claim lived only in `_trust_breakdown` prose, so nothing
/// caught the three ways it could rot:
///   - an entry added to `axioms` and categorized in NO bucket (silently
///     inflating the census while the headline still reads 3);
///   - an entry in TWO buckets (double-counted, so the sum lies); or
///   - `genuine_foundational_axiom_count` drifting off its own name list.
///
/// This makes the partition EXHAUSTIVE (union == the full census) and DISJOINT,
/// and pins the foundational set to exactly the finish-line triple. Combined
/// with `no_new_admitted_axioms_in_spec` (which ties the golden to the LIVE
/// kernel env), a new axiom must now be both explicitly admitted AND explicitly
/// categorized to land — it cannot hide in a bucket boundary.
#[test]
fn trust_partition_is_exhaustive_disjoint_and_headline_is_three() {
    let golden = load_golden();
    let tb = &golden.trust_breakdown;

    let genuine: BTreeSet<&str> = tb
        .genuine_foundational_axioms
        .iter()
        .map(String::as_str)
        .collect();
    let quotient: BTreeSet<&str> = tb
        .quotient_primitives_not_axioms
        .iter()
        .map(String::as_str)
        .collect();
    let tripwires: BTreeSet<&str> = tb
        .honesty_tripwires_anti_trust
        .iter()
        .map(String::as_str)
        .collect();

    // The headline must equal its own list, and that list must be exactly the
    // 3-axiom finish line — not a superset that grew quietly.
    assert_eq!(
        tb.genuine_foundational_axiom_count,
        genuine.len(),
        "genuine_foundational_axiom_count disagrees with genuine_foundational_axioms"
    );
    let finish_line: BTreeSet<&str> = ["Classical.choice", "Quot.sound", "propext"]
        .into_iter()
        .collect();
    assert_eq!(
        genuine, finish_line,
        "the foundational set must be exactly {{propext, Quot.sound, Classical.choice}}; \
         a change here is a change to the TCB and must be argued in the certificate, \
         not slipped into a data file"
    );

    // Pairwise disjoint: no entry may be counted under two headings.
    for (a_name, a, b_name, b) in [
        ("genuine", &genuine, "quotient", &quotient),
        ("genuine", &genuine, "tripwires", &tripwires),
        ("quotient", &quotient, "tripwires", &tripwires),
    ] {
        let overlap: Vec<&&str> = a.intersection(b).collect();
        assert!(
            overlap.is_empty(),
            "{a_name} and {b_name} buckets overlap on {overlap:?} — the census sum would double-count"
        );
    }

    // Exhaustive: the three buckets must cover the census exactly.
    let categorized: BTreeSet<&str> = genuine
        .union(&quotient)
        .copied()
        .collect::<BTreeSet<&str>>()
        .union(&tripwires)
        .copied()
        .collect();
    let census: BTreeSet<&str> = golden.axioms.iter().map(|a| a.name.as_str()).collect();

    let uncategorized: Vec<&&str> = census.difference(&categorized).collect();
    assert!(
        uncategorized.is_empty(),
        "census entries in NO trust bucket: {uncategorized:?}. Every admitted entry must be \
         classified as a foundational axiom, a Quot type-former, or an anti-trust tripwire — \
         an uncategorized entry inflates the census while the headline still claims 3."
    );
    let phantom: Vec<&&str> = categorized.difference(&census).collect();
    assert!(
        phantom.is_empty(),
        "trust buckets name entries absent from the census: {phantom:?}"
    );

    assert_eq!(
        genuine.len() + quotient.len() + tripwires.len(),
        golden.count,
        "3/4/4 partition does not sum to the recorded census count"
    );
}

/// Cross-check: every live kernel-env axiom's recorded origin label is one the
/// ratchet understands. This keeps the golden's `origin` field meaningful
/// (`FlagAxiom` vs the C1 `PendingLeaf` vs the M1 `EnvInjected`) without making
/// the test equality-based.
#[test]
fn ratchet_origin_labels_are_known() {
    let spec = build_spec_with_stack();
    for a in live_env_axioms(&spec) {
        let label = origin_label(a.origin);
        assert!(
            matches!(label, "FlagAxiom" | "PendingLeaf" | "EnvInjected" | "Other"),
            "unexpected origin label {label} for live env axiom {}",
            a.name
        );
    }
}
