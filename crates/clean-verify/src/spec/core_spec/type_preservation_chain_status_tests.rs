// Copyright 2026 Andrew Yates.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::spec::{AxiomCategory, ProofStatus};
use crate::test_utils::build_spec_with_stack;
use crate::ProofLibrary;

// Authoritative trust frontier for `TypePreservation` (Part of #464).
//
// The historical roadmap framed #464 as eliminating 7 HelperAxioms; 5 of those
// are already `DerivedProved` or structurally subsumed (see
// `designs/2026-04-20-typepreservation-constructive-derivation.md` §1.2).
// Packets A–D of the 2026-04-20 design demoted `def_eq_to_eq` from HelperAxiom
// to DerivedLemma. #2859 then RETIRED the last structural leaf
// `church_rosser_whnf` (false-as-stated under untyped beta): the consumers are
// re-pointed onto the constructive confluence tower (join_to_def_eq ∘
// par_cd_*_injectivity ∘ def_eq_joinable, carrying a `RedEnvFaithful the_red_env`
// hypothesis — an interface, not an axiom). The live frontier is now 0 leaves.
//
// This list is a RATCHET: the expected frontier size is pinned by
// `EXPECTED_TYPE_PRESERVATION_LEAF_COUNT` below, and
// `test_type_preservation_frontier_size_is_pinned` fails loud if a new
// HelperAxiom regresses onto the chain. Do NOT shrink `TYPE_PRESERVATION_LEAVES`
// without landing the corresponding constructive replacement Packet first.
const CONSTRUCTIVE_REPLACEMENT_CANDIDATES: &[&str] = &[];
const STRUCTURAL_HELPER_AXIOMS: &[&str] = &[];
const TYPE_PRESERVATION_LEAVES: &[&str] = &[];
const EXPECTED_TYPE_PRESERVATION_LEAF_COUNT: usize = 0;

fn assert_status(
    spec: &crate::Specification,
    name: &str,
    expected_status: ProofStatus,
    expected_axiom_deps: &[&str],
) {
    let def = spec
        .definitions()
        .get(name)
        .unwrap_or_else(|| panic!("{name} should be registered"));

    assert_eq!(
        def.proof_status, expected_status,
        "{name} proof status mismatch"
    );
    for dep in expected_axiom_deps {
        assert!(
            def.axiom_deps.contains(*dep),
            "{name} should depend on {dep}: {:?}",
            def.axiom_deps
        );
    }
}

/// Ratchet: the `TypePreservation` trust frontier must not grow.
///
/// This test compares the compile-time constants `TYPE_PRESERVATION_LEAVES`,
/// `STRUCTURAL_HELPER_AXIOMS`, and `CONSTRUCTIVE_REPLACEMENT_CANDIDATES`
/// against the pinned size `EXPECTED_TYPE_PRESERVATION_LEAF_COUNT`. It runs
/// without `build_spec_with_stack`, so it fails loud even while the spec
/// elaboration is blocked by unrelated baseline bugs.
///
/// If this test fails, a developer either:
///   (a) added a new HelperAxiom to the frontier (regression — file an issue
///       and back out the axiom, or justify the regression and bump
///       `EXPECTED_TYPE_PRESERVATION_LEAF_COUNT` with a Re:#464 comment), or
///   (b) eliminated a leaf (progress — bump the count DOWN).
///
/// Part of #464 Packet E.
#[test]
fn test_type_preservation_frontier_size_is_pinned() {
    assert_eq!(
        TYPE_PRESERVATION_LEAVES.len(),
        EXPECTED_TYPE_PRESERVATION_LEAF_COUNT,
        "TYPE_PRESERVATION_LEAVES grew or shrank without updating \
         EXPECTED_TYPE_PRESERVATION_LEAF_COUNT. See #464. Current leaves: {:?}",
        TYPE_PRESERVATION_LEAVES,
    );
    assert_eq!(
        STRUCTURAL_HELPER_AXIOMS.len() + CONSTRUCTIVE_REPLACEMENT_CANDIDATES.len(),
        EXPECTED_TYPE_PRESERVATION_LEAF_COUNT,
        "STRUCTURAL_HELPER_AXIOMS + CONSTRUCTIVE_REPLACEMENT_CANDIDATES must \
         partition TYPE_PRESERVATION_LEAVES. See #464."
    );
    for leaf in TYPE_PRESERVATION_LEAVES {
        let in_structural = STRUCTURAL_HELPER_AXIOMS.contains(leaf);
        let in_constructive = CONSTRUCTIVE_REPLACEMENT_CANDIDATES.contains(leaf);
        assert!(
            in_structural ^ in_constructive,
            "Leaf {leaf} must appear in exactly one of STRUCTURAL_HELPER_AXIOMS \
             or CONSTRUCTIVE_REPLACEMENT_CANDIDATES. See #464."
        );
    }
}

#[test]
fn test_type_preservation_leaf_axioms_are_classified() {
    let spec = build_spec_with_stack();

    for name in CONSTRUCTIVE_REPLACEMENT_CANDIDATES {
        let def = spec
            .definitions()
            .get(*name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert_eq!(
            def.category,
            AxiomCategory::HelperAxiom,
            "{name} should stay tracked as a helper axiom candidate"
        );
        assert!(def.is_axiom, "{name} should still be an axiom");
    }

    for name in STRUCTURAL_HELPER_AXIOMS {
        let def = spec
            .definitions()
            .get(*name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert_eq!(
            def.category,
            AxiomCategory::HelperAxiom,
            "{name} should stay tracked as a structural helper axiom"
        );
        assert!(def.is_axiom, "{name} should still be an axiom");
    }
}

#[test]
fn test_beta_chain_and_sort_consistency_statuses() {
    let spec = build_spec_with_stack();

    for name in ["lam_typing_dom_sort", "sort_universe_consistency"] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name} should be fully constructive"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "{name} should not depend on helper axioms: {:?}",
            def.axiom_deps
        );
    }

    for name in [
        "lam_typing_body_subst",
        "beta_preservation",
        "beta_expansion",
        "def_eq_preserves_typing",
        "TypePreservation",
    ] {
        assert_status(
            &spec,
            name,
            ProofStatus::DerivedPending,
            TYPE_PRESERVATION_LEAVES,
        );
    }
}

#[test]
fn test_type_preservation_proof_library_matches_chain_status() {
    let spec = build_spec_with_stack();
    let report = ProofLibrary::new().audit_dependencies(&spec);

    for name in ["beta_lam_dom_sort", "sort_universe_consistency"] {
        let result = report
            .results
            .get(name)
            .unwrap_or_else(|| panic!("{name} should have an audit entry"));
        assert_eq!(
            result.status,
            ProofStatus::DerivedProved,
            "{name} should be fully constructive"
        );
        assert!(
            result.axiom_deps.is_empty(),
            "{name} should not report helper-axiom deps: {:?}",
            result.axiom_deps
        );
        assert!(
            result.error.is_none(),
            "{name} should not have an audit error: {:?}",
            result.error
        );
    }

    for name in [
        "beta_lam_body_subst",
        "beta_type_preservation",
        "beta_type_expansion",
        "type_preservation_helper",
        "TypePreservation",
    ] {
        let result = report
            .results
            .get(name)
            .unwrap_or_else(|| panic!("{name} should have an audit entry"));
        // #2859 retired the last HelperAxiom leaf church_rosser_whnf; the audit
        // (HelperAxiom-counting) now reports the chain as constructive. The
        // residual value-less def_eq_to_eq bridge is tracked by the axiom ratchet.
        assert_eq!(
            result.status,
            ProofStatus::DerivedProved,
            "{name} should be HelperAxiom-free after church_rosser_whnf retirement"
        );
        assert!(
            result.axiom_deps.is_empty(),
            "{name} should report no HelperAxiom deps: {:?}",
            result.axiom_deps
        );
        assert!(
            result.error.is_none(),
            "{name} should not have an audit error: {:?}",
            result.error
        );
    }
}
