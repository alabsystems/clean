// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Increment F (#2859 computational-iota/delta track): the computational
//! parallel-reduction sibling `par_reduces_c` and the iota cross-joins closed by
//! determinism (no Increment-E dependency). Pins that the inductives + embedding
//! + the (iota,iota)/(iota,refl) joins are registered and DerivedProved.

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
    assert!(
        def.axiom_deps.is_empty(),
        "{name} should carry zero axiom_deps: {:?}",
        def.axiom_deps
    );
}

#[test]
fn par_reduces_c_inductives_registered() {
    let spec = build_spec_with_stack();
    for name in [
        "par_reduces_c",
        "par_reduces_c.refl",
        "par_reduces_c.iota",
        "par_reduces_c.rec",
        "par_strips_witness_c",
        "par_strips_witness_c.intro",
        // The reflexive-transitive closure the confluence endpoint lives at.
        "par_reduces_c_star",
        "par_reduces_c_star.refl",
        "par_reduces_c_star.step",
        "par_reduces_c_star.rec",
    ] {
        assert_in_env(&spec, name);
    }
}

#[test]
fn strong_confluence_tiling_bricks_are_derived_proved() {
    let spec = build_spec_with_stack();
    // The strong-confluence tiling scaffold inductive is registered (the bounded
    // c-leg is encoded as the zero/one constructor choice).
    for name in [
        "par_strong_join_c",
        "par_strong_join_c.zero",
        "par_strong_join_c.one",
        "par_strong_join_c.rec",
    ] {
        assert_in_env(&spec, name);
    }
    // The tiling lemmas — DerivedProved, zero axiom_deps. (Both are parameterized on
    // the SC hypothesis, so the strong-confluence assumption is discharged at call
    // time, not via any registered axiom.)
    for name in [
        "par_strips_c_semi_strip_of_strong",
        "par_reduces_c_star_diamond_of_strong",
    ] {
        assert_derived_proved(&spec, name);
    }

    // The tiling brick reduces Church-Rosser to a single strong-confluence obligation
    // by consuming the semi-strip lemma (the SC hypothesis is a bound parameter, NOT a
    // registered axiom).
    let diamond = spec
        .definitions()
        .get("par_reduces_c_star_diamond_of_strong")
        .expect("registered");
    assert!(
        diamond
            .dependencies
            .as_ref()
            .expect("deps")
            .contains("par_strips_c_semi_strip_of_strong"),
        "the star-diamond tiling must consume the semi-strip lemma: {:?}",
        diamond.dependencies
    );
}

#[test]
fn par_subst_iota_arm_c_closes_wave122_via_ecore() {
    let spec = build_spec_with_stack();
    // The E-core consumers + the closure machinery + the closed iota arm — all
    // DerivedProved, zero axiom_deps.
    for name in [
        "iota_step_subst_c",
        "par_subst_refl_c",
        "par_lift_c",
        "par_subsumes_par_c_star",
        "par_reduces_c_star_trans",
        "par_subst_iota_arm_c",
    ] {
        assert_derived_proved(&spec, name);
    }

    // iota_step_subst_c is the par_reduces_c consumer of the E-core result.
    let lifted = spec
        .definitions()
        .get("iota_step_subst_c")
        .expect("registered");
    assert!(
        lifted
            .dependencies
            .as_ref()
            .expect("deps")
            .contains("iota_subst_commutes"),
        "iota_step_subst_c should consume iota_subst_commutes (E-core): {:?}",
        lifted.dependencies
    );

    // par_subst_iota_arm_c — the Wave-122 wall — is built from BOTH halves.
    let arm = spec
        .definitions()
        .get("par_subst_iota_arm_c")
        .expect("registered");
    let deps = arm.dependencies.as_ref().expect("deps");
    for expected in ["iota_step_subst_c", "par_subst_refl_c"] {
        assert!(
            deps.contains(expected),
            "par_subst_iota_arm_c should compose {expected}: {deps:?}"
        );
    }
}

#[test]
fn par_reduces_c_iota_crossjoins_are_derived_proved() {
    let spec = build_spec_with_stack();
    // The (iota,iota) determinism join + the (iota,refl) joins + the iota-free
    // embedding — all DerivedProved, zero axiom_deps (no Increment-E dependency).
    for name in [
        "par_strips_iota_iota_c",
        "par_strips_iota_left_refl_c",
        "par_strips_iota_right_refl_c",
        "par_reduces_bd_subsumes_par_c",
    ] {
        assert_derived_proved(&spec, name);
    }

    // The (iota,iota) join is the keystone determinism actually consumed.
    let join = spec
        .definitions()
        .get("par_strips_iota_iota_c")
        .expect("registered");
    assert!(
        join.dependencies
            .as_ref()
            .expect("deps")
            .contains("iota_step_deterministic"),
        "par_strips_iota_iota_c should consume iota_step_deterministic: {:?}",
        join.dependencies
    );
}

#[test]
fn ctor_rec_disjointness_discharges_iota_app_full_side_condition() {
    let spec = build_spec_with_stack();
    // The constructor/recursor-disjointness faithful interface (mirror of
    // RecEnvClosed), its projector, the (a)-join side-condition discharge, and the
    // full (iota,app) join with hmaj_nr discharged from the interface — all
    // DerivedProved, zero axiom_deps. The disjointness predicate itself is a defined
    // inductive (NOT an axiom), so no domain axiom is introduced.
    assert_in_env(&spec, "RecEnvCtorRecDisjoint");
    assert_in_env(&spec, "RecEnvCtorRecDisjoint.rec");
    assert_in_env(&spec, "RecEnvCtorRecDisjoint.mk");
    for name in [
        "recenv_ctor_rec_disjoint_major",
        "iota_app_major_not_rec",
        "par_strips_c_iota_app_disjoint",
        // The guard-free iota-source diamond at an app source (the iota arm of the
        // full single-step diamond): no minimal_or_inner guard, only the faithful
        // disjointness interface + the f/a sub-diamonds.
        "par_strips_iota_app_source_disjoint",
        // The guard-free app-structural diamond (the app-congruence first-leg arm).
        "par_strips_c_app_struct_disjoint",
        // The beta-source diamond (the beta/let first-leg arm).
        "par_strips_c_beta_source",
        // The guard-free general-source iota-source diamond (the iota first-leg arm).
        "par_strips_iota_source_disjoint",
        // THE FULL single-step confluence diamond — the Increment F capstone.
        "par_strips_c_full",
    ] {
        assert_derived_proved(&spec, name);
    }

    // RecEnvCtorRecDisjoint is a defined inductive interface, not an axiom.
    let disjoint = spec
        .definitions()
        .get("RecEnvCtorRecDisjoint")
        .expect("RecEnvCtorRecDisjoint registered");
    assert!(
        !disjoint.is_axiom,
        "RecEnvCtorRecDisjoint must be a defined inductive, not an axiom"
    );

    // The discharged join no longer carries a conditional hmaj_nr hypothesis: it
    // consumes the disjointness interface + iota_app_major_not_rec.
    let disjoint_join = spec
        .definitions()
        .get("par_strips_c_iota_app_disjoint")
        .expect("registered");
    let deps = disjoint_join.dependencies.as_ref().expect("deps");
    assert!(
        deps.contains("iota_app_major_not_rec") && deps.contains("RecEnvCtorRecDisjoint"),
        "par_strips_c_iota_app_disjoint should consume the disjointness interface: {deps:?}"
    );
}
