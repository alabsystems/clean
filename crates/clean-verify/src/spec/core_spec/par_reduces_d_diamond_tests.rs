// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the δ single-step strong diamond and unconditional δ CR (#2859
//! Increment H++, Stage 4).

use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::test_utils::run_with_stack;
use crate::Specification;

/// Build the substitution subset of the spec. `add_par_reduces_d_diamond` is in the
/// substitution bundle (`in_substitution: true` in `bundles.rs`).
fn build_d_diamond_spec() -> Specification {
    run_with_stack(|| {
        Specification::new_substitution_test_spec().expect("substitution test spec should build")
    })
}

/// Every δ-diamond brick is DerivedProved with zero axiom deps and a proof term.
#[test]
fn test_delta_diamond_bricks_are_derived_proved_zero_axiom() {
    let spec = build_d_diamond_spec();
    for name in [
        // Type-valued inversion substrate (Brick D0)
        "delta_reduct_some_inv_type",
        "delta_step_head_none_absurd_type",
        "delta_step_app_inv_type",
        // bvar/const discriminators (Brick D1)
        "bvar_ne_app",
        "bvar_ne_lam",
        "bvar_ne_pi",
        "const_ne_app",
        "const_ne_lam",
        "const_ne_pi",
        // delta_cong inversions (Brick D2)
        "delta_cong_app_inv",
        "delta_cong_lam_inv",
        "delta_cong_pi_inv",
        "delta_cong_let_inv",
        "delta_cong_sort_absurd",
        "delta_cong_bvar_absurd",
        "delta_cong_const_inv",
        // The single-step strong diamond (Brick D3)
        "delta_cong_diamond",
        // The UNCONDITIONAL δ Church-Rosser (Brick D4)
        "delta_cong_star_diamond",
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert!(!def.is_axiom, "{name} should not be an axiom");
        assert_eq!(
            def.category,
            AxiomCategory::DerivedLemma,
            "{name} should be a DerivedLemma"
        );
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name} should be DerivedProved"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "{name} should carry no axiom dependencies: {:?}",
            def.axiom_deps
        );
        assert!(
            def.value_src.is_some(),
            "{name} should have a constructive proof term"
        );
    }
}
