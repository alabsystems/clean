// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the micro totality contrast. These build the FULL spec, because
//! `MicroVerifies` is registered by a full-only stage — measured 2026-09-17 at
//! 18m30s / 2.75 GB peak, which fits this box's 4 GB `heavy_gate` budget.

use super::*;
use crate::test_utils::parse_check;

fn full_spec() -> Specification {
    crate::test_utils::build_spec_with_stack()
}

/// Both sources parse. Microseconds, versus a full spec build.
#[test]
fn test_micro_totality_contrast_sources_parse() {
    parse_check(&format!(
        "def mv_not_total : {} := {}",
        ty_mv_not_total(),
        val_mv_not_total()
    ))
    .expect("mv_not_total must parse");
    parse_check(&format!(
        "def mv_totality_contrast : {} := {}",
        ty_mv_totality_contrast(),
        val_mv_totality_contrast()
    ))
    .expect("mv_totality_contrast must parse");
}

/// The two shapes are genuinely opposite: one asserts totality, the other sends
/// totality to `Empty`, and they are the SAME totality shape on each side of
/// the pair. Measured from the rung's own strings, so a later edit that quietly
/// weakened one half would fail here.
#[test]
fn test_micro_totality_contrast_is_a_genuine_opposition() {
    let contrast = ty_mv_totality_contrast();
    assert!(
        contrast.contains(TY_MV_TOTAL) && contrast.contains("-> Empty)"),
        "the contrast no longer sends the faithful family's totality to Empty"
    );
    assert!(
        contrast.contains(TY_MHT_TOTAL),
        "the contrast no longer carries the degenerate band's totality"
    );
    assert!(
        ty_mv_not_total().contains(TY_MV_TOTAL),
        "mv_not_total no longer negates the same totality shape the contrast carries"
    );
}

/// Both constants are registered in the FULL spec and re-verify.
#[test]
fn test_micro_totality_contrast_registered_and_reverifies() {
    let spec = full_spec();
    for name in ["mv_not_total", "mv_totality_contrast"] {
        assert!(
            spec.definitions().contains_key(name)
                || spec
                    .env()
                    .get_const(&clean_kernel::Name::from_string(name))
                    .is_some(),
            "{name} is not registered in the full spec"
        );
        spec.verify_definition(name)
            .unwrap_or_else(|e| panic!("{name} does not re-verify: {e:?}"));
    }
}

/// CENSUS. Both rest on no non-foundational axiom.
#[test]
fn test_micro_totality_contrast_axiom_closure_is_empty() {
    let spec = full_spec();
    for name in ["mv_not_total", "mv_totality_contrast"] {
        let closure = crate::spec_axiom_closure::computed_axiom_closure(&spec, name);
        assert!(
            closure.is_empty(),
            "{name} rests on non-foundational axioms: {closure:?}"
        );
        let markers = crate::spec_axiom_closure::computed_trust_markers(&spec, name);
        assert!(
            markers.is_empty(),
            "{name} reaches a trust marker: {markers:?}"
        );
    }
}

/// THE POINT, checked against the live environment rather than against prose:
/// the degenerate band really is total and the faithful family really is not,
/// and BOTH are present. If `micro_has_type_total` ever stops existing the
/// contrast is meaningless; if `mv_bvar_nil_reject` does, `mv_not_total` has
/// lost its only input.
#[test]
fn test_micro_totality_contrast_both_halves_are_live() {
    let spec = full_spec();
    for required in [
        "micro_has_type_total",
        "mv_bvar_nil_reject",
        "MicroVerifies",
    ] {
        assert!(
            spec.definitions().contains_key(required)
                || spec
                    .env()
                    .get_const(&clean_kernel::Name::from_string(required))
                    .is_some(),
            "{required} is missing — the contrast has lost a half"
        );
    }
}
