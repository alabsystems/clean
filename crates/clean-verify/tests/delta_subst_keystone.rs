// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Increment G (#2859 computational-iota/delta track) — the δ substitution /
//! lift commutation substrate, the delta analogue of the Increment E iota
//! E-core (`iota_subst_commutes` / `iota_lift_commutes`).
//!
//! Pins that the `DefEnvClosed` / `DefEnvLiftClosed` faithful interfaces and
//! their projectors (`defenv_closed_val` / `defenv_lift_closed_val`), the delta
//! reduct equations (`delta_reduct_inst_eq` / `delta_reduct_lift_eq`), and the
//! delta E-core keystones (`delta_subst_commutes` / `delta_lift_commutes`) are
//! registered, kernel-checked, DerivedProved, and carry zero axiom_deps.

use clean_kernel::Name;
use clean_verify::spec::{ProofStatus, Specification};
use clean_verify::test_utils::build_spec_with_stack;

fn assert_in_env(spec: &Specification, name: &str) {
    assert!(
        spec.env().get_const(&Name::from_string(name)).is_some(),
        "{name} should be registered in the spec environment"
    );
}

fn assert_derived_proved_zero_axioms(spec: &Specification, name: &str) {
    let def = spec
        .definitions()
        .get(name)
        .unwrap_or_else(|| panic!("{name} should be registered"));
    assert!(!def.is_axiom, "{name} must not be an axiom");
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "{name} should be DerivedProved (closed, kernel-checked term)"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "{name} should carry zero axiom_deps: {:?}",
        def.axiom_deps
    );
}

/// The DefEnvClosed / DefEnvLiftClosed faithful interfaces + their projectors are
/// registered (kernel-checked) and the projectors are DerivedProved, zero axioms.
#[test]
fn defenv_closure_interfaces_registered() {
    let spec = build_spec_with_stack();
    for name in [
        "DefEnvClosed",
        "DefEnvClosed.mk",
        "DefEnvLiftClosed",
        "DefEnvLiftClosed.mk",
        "defenv_closed_val",
        "defenv_lift_closed_val",
    ] {
        assert_in_env(&spec, name);
    }
    for name in ["defenv_closed_val", "defenv_lift_closed_val"] {
        assert_derived_proved_zero_axioms(&spec, name);
    }
}

/// Brick B: the instantiate_at delta commutation — the reduct equation
/// `delta_reduct_inst_eq` and the E-core keystone `delta_subst_commutes` are
/// DerivedProved with zero axiom_deps (kernel-checked closed terms).
#[test]
fn delta_subst_commutes_is_derived_proved() {
    let spec = build_spec_with_stack();
    for name in ["delta_reduct_inst_eq", "delta_subst_commutes"] {
        assert_derived_proved_zero_axioms(&spec, name);
    }
    // delta_subst_commutes inverts via the CPS inverter and closes the reduct slot
    // via delta_reduct_inst_eq.
    let def = spec
        .definitions()
        .get("delta_subst_commutes")
        .expect("registered");
    let deps = def.dependencies.as_ref().expect("deps");
    for expected in ["delta_reduct_some_inv", "delta_reduct_inst_eq"] {
        assert!(
            deps.contains(expected),
            "delta_subst_commutes should depend on {expected}: {deps:?}"
        );
    }
}

/// Brick C: the lift_at delta commutation — the reduct equation
/// `delta_reduct_lift_eq` and the LIFT E-core keystone `delta_lift_commutes` are
/// DerivedProved with zero axiom_deps (kernel-checked closed terms). Unconditional
/// (no head-const guard), the lift mirror of Brick B.
#[test]
fn delta_lift_commutes_is_derived_proved() {
    let spec = build_spec_with_stack();
    for name in ["delta_reduct_lift_eq", "delta_lift_commutes"] {
        assert_derived_proved_zero_axioms(&spec, name);
    }
    let def = spec
        .definitions()
        .get("delta_lift_commutes")
        .expect("registered");
    let deps = def.dependencies.as_ref().expect("deps");
    for expected in ["delta_reduct_some_inv", "delta_reduct_lift_eq"] {
        assert!(
            deps.contains(expected),
            "delta_lift_commutes should depend on {expected}: {deps:?}"
        );
    }
}
