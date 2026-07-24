// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Increment F+ (#2859 computational-iota/delta track): the complete development
//! `cd` and its term-inspection helpers are registered and kernel-check.

use clean_kernel::Name;
use clean_verify::spec::{AxiomCategory, ProofStatus, Specification};
use clean_verify::test_utils::build_spec_with_stack;

fn assert_in_env(spec: &Specification, name: &str) {
    assert!(
        spec.env().get_const(&Name::from_string(name)).is_some(),
        "{name} should be registered in the spec environment"
    );
}

fn assert_derived_proved(spec: &Specification, name: &str) {
    let def = spec
        .definitions()
        .get(name)
        .unwrap_or_else(|| panic!("{name} should be registered"));
    assert!(!def.is_axiom, "{name} must not be an axiom");
    assert_eq!(def.category, AxiomCategory::DerivedLemma, "{name} category");
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "{name} should be DerivedProved"
    );
    assert!(def.axiom_deps.is_empty(), "{name} zero axiom_deps");
}

#[test]
fn complete_development_cd_registered() {
    let spec = build_spec_with_stack();
    // The complete development function + its helpers — all kernel-check (the whole
    // spec builds, so cd's structural KExpr.rec + the Bool/OptionType dispatch and
    // iota_reduct/instantiate references all typecheck).
    for name in ["opt_default", "kexpr_is_lam", "kexpr_lam_body", "cd"] {
        assert_in_env(&spec, name);
    }
}

#[test]
fn cd_unfold_equations_are_derived_proved() {
    let spec = build_spec_with_stack();
    // The cd defining-equation unfolds (Eq.refl — confirms the kernel computes
    // through cd's structural KExpr.rec / Bool.rec / the lam-body projector).
    for name in ["cd_lam", "cd_pi", "cd_app", "cd_app_lam", "kexpr_lam_cases"] {
        assert_derived_proved(&spec, name);
    }
}

#[test]
fn below_boundary_spine_cong_bricks_are_zero_axiom_derived_proved() {
    let spec = build_spec_with_stack();
    // The L2 wall, CLOSED (#2859 Increment F+): the below-boundary arithmetic
    // discharge bricks + the boundary-guarded spine congruence itself. All
    // DerivedProved with zero axiom_deps (genuine kernel-checked proof terms).
    for name in [
        "le_succ_zero_empty",
        "le_succ_self_empty",
        "iota_step_below_boundary_absurd",
        "par_reduces_p_spine_cong_below_boundary",
        // The constructor-headed-major companion (no-recmeta guard).
        "iota_step_no_recmeta_absurd",
        "par_reduces_p_spine_cong_no_recmeta",
    ] {
        assert_derived_proved(&spec, name);
    }
    // The Type-valued box that lets the AndType-product motive carry the (Prop)
    // head-preservation fact is registered (a genuine one-ctor inductive, not an
    // axiom).
    assert_in_env(&spec, "HeadConstBox");
    assert_in_env(&spec, "HeadConstBox.mk");
    assert_in_env(&spec, "HeadConstBox.rec");
}
