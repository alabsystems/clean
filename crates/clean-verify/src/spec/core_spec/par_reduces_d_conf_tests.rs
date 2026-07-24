// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the δ Huet strong-confluence tiling (#2859 Increment H++, Stage 4).

use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::test_utils::run_with_stack;
use crate::Specification;

/// Build the substitution subset of the spec. `add_par_reduces_d_conf` is in the
/// substitution bundle (`in_substitution: true` in `bundles.rs`).
fn build_d_conf_spec() -> Specification {
    run_with_stack(|| {
        Specification::new_substitution_test_spec().expect("substitution test spec should build")
    })
}

/// `par_strong_join_d` inductive is registered with its recursor and two ctors.
#[test]
fn test_par_strong_join_d_registered() {
    let spec = build_d_conf_spec();
    for name in [
        "par_strong_join_d",
        "par_strong_join_d.rec",
        "par_strong_join_d.zero",
        "par_strong_join_d.one",
    ] {
        assert!(
            spec.definitions().contains_key(name),
            "{name} should be registered"
        );
    }
}

/// The two δ strong-confluence tiling lemmas plus the nine par_strong_join_d
/// congruence lifts (app/lam/pi two-slot, let_ three-slot) are DerivedProved
/// with zero axiom deps.
#[test]
fn test_delta_sc_tiling_lemmas_are_derived_proved_zero_axiom() {
    let spec = build_d_conf_spec();
    for name in [
        "delta_reduct_app_eq",
        "delta_step_app_cong",
        "delta_step_app_inv",
        "delta_strips_semi_strip_of_strong",
        "delta_cong_star_diamond_of_strong",
        "par_strong_join_d_app_f",
        "par_strong_join_d_app_a",
        "par_strong_join_d_lam_t",
        "par_strong_join_d_lam_b",
        "par_strong_join_d_pi_d",
        "par_strong_join_d_pi_b",
        "par_strong_join_d_let_t",
        "par_strong_join_d_let_v",
        "par_strong_join_d_let_b",
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
