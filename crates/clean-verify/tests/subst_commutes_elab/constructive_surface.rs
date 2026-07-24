// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_verify::spec::ProofStatus;
use clean_verify::Specification;

use super::{assert_exact_axiom_deps, build_substitution_spec_with_stack};

#[test]
fn instantiate_at_structural_helpers_are_constructive() {
    let spec = build_substitution_spec_with_stack();

    for name in [
        "instantiate_at_app",
        "instantiate_at_lam",
        "instantiate_at_pi",
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("Missing definition {name}"));
        assert!(
            def.value_src.is_some(),
            "{name} should now carry a direct proof term"
        );
        assert!(!def.is_axiom, "{name} should no longer be a helper axiom");
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name} should be fully derived by direct reduction"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "{name} should have no remaining helper dependencies: {:?}",
            def.axiom_deps
        );
    }
}

fn assert_instantiate_app_lam_eq_surface(spec: &Specification) {
    let app_lam_eq = spec
        .definitions()
        .get("instantiate_app_lam_eq")
        .expect("instantiate_app_lam_eq should exist");
    assert!(
        app_lam_eq.value_src.is_some(),
        "instantiate_app_lam_eq should have a proof term"
    );
    assert!(
        !app_lam_eq.is_axiom,
        "instantiate_app_lam_eq should not be an axiom"
    );
    assert_eq!(
        app_lam_eq.proof_status,
        ProofStatus::DerivedProved,
        "instantiate_app_lam_eq should be DerivedProved (structural helpers now constructive)"
    );
}

fn assert_nat_sub_surface(spec: &Specification) {
    let nat_sub_succ_succ = spec
        .definitions()
        .get("nat_sub_succ_succ")
        .expect("nat_sub_succ_succ should exist");
    assert!(
        nat_sub_succ_succ.value_src.is_some(),
        "nat_sub_succ_succ should now have a proof term"
    );
    assert!(
        !nat_sub_succ_succ.is_axiom,
        "nat_sub_succ_succ should no longer be tracked as an axiom"
    );
    assert_eq!(
        nat_sub_succ_succ.proof_status,
        ProofStatus::DerivedProved,
        "nat_sub_succ_succ should be fully constructive"
    );

    let nat_sub_self = spec
        .definitions()
        .get("nat_sub_self")
        .expect("nat_sub_self should exist");
    assert!(
        nat_sub_self.value_src.is_some(),
        "nat_sub_self should now have a proof term"
    );
    assert!(
        !nat_sub_self.is_axiom,
        "nat_sub_self should no longer be tracked as a helper axiom"
    );
    assert_eq!(
        nat_sub_self.proof_status,
        ProofStatus::DerivedProved,
        "nat_sub_self should be fully constructive"
    );
    assert!(
        nat_sub_self.axiom_deps.is_empty(),
        "nat_sub_self should not retain helper-axiom blockers: {:?}",
        nat_sub_self.axiom_deps
    );
}

fn assert_instantiate_bvar_at_eq_surface(spec: &Specification) {
    let instantiate_bvar_at_eq = spec
        .definitions()
        .get("instantiate_bvar_at_eq")
        .expect("instantiate_bvar_at_eq should exist");
    assert!(
        instantiate_bvar_at_eq.value_src.is_some(),
        "instantiate_bvar_at_eq should now have a proof term"
    );
    assert!(
        !instantiate_bvar_at_eq.is_axiom,
        "instantiate_bvar_at_eq should no longer be tracked as a helper axiom"
    );
    assert_eq!(
        instantiate_bvar_at_eq.proof_status,
        ProofStatus::DerivedProved,
        "instantiate_bvar_at_eq should now be fully constructive"
    );
    assert!(
        instantiate_bvar_at_eq.axiom_deps.is_empty(),
        "instantiate_bvar_at_eq should not retain helper blockers: {:?}",
        instantiate_bvar_at_eq.axiom_deps
    );
}

fn assert_lift_at_amount_zero_surface(spec: &Specification) {
    let lift_at_amount_zero = spec
        .definitions()
        .get("lift_at_amount_zero")
        .expect("lift_at_amount_zero should exist");
    assert!(
        lift_at_amount_zero.value_src.is_some(),
        "lift_at_amount_zero should now have a KExpr.rec proof term"
    );
    assert!(
        !lift_at_amount_zero.is_axiom,
        "lift_at_amount_zero should no longer be a helper axiom"
    );
    assert_eq!(
        lift_at_amount_zero.proof_status,
        ProofStatus::DerivedProved,
        "lift_at_amount_zero should be fully constructive via KExpr.rec"
    );
    assert!(
        lift_at_amount_zero.axiom_deps.is_empty(),
        "lift_at_amount_zero should have no remaining helper blockers: {:?}",
        lift_at_amount_zero.axiom_deps
    );

    let lift_zero = spec
        .definitions()
        .get("lift_zero_identity")
        .expect("lift_zero_identity should exist");
    assert!(
        lift_zero.value_src.is_some(),
        "lift_zero_identity should now have a proof term"
    );
    assert!(
        !lift_zero.is_axiom,
        "lift_zero_identity should no longer be a helper axiom"
    );
    assert_eq!(
        lift_zero.proof_status,
        ProofStatus::DerivedProved,
        "lift_zero_identity should be derived from lift_at_amount_zero"
    );
}

fn assert_instantiate_bvar_zero_surface(spec: &Specification) {
    let instantiate_bvar_zero = spec
        .definitions()
        .get("instantiate_bvar_zero")
        .expect("instantiate_bvar_zero should exist");
    assert_eq!(
        instantiate_bvar_zero.proof_status,
        ProofStatus::DerivedProved,
        "instantiate_bvar_zero should now be fully constructive (lift_at_amount_zero resolved)"
    );
    assert!(
        !instantiate_bvar_zero.axiom_deps.contains("nat_sub_self"),
        "instantiate_bvar_zero should not treat nat_sub_self as a blocker"
    );
    assert!(
        !instantiate_bvar_zero
            .axiom_deps
            .contains("lift_at_amount_zero"),
        "instantiate_bvar_zero should no longer treat lift_at_amount_zero as a blocker"
    );
    assert_exact_axiom_deps(instantiate_bvar_zero, &[], "instantiate_bvar_zero");
}

#[test]
fn instantiate_app_lam_eq_surface_is_constructive() {
    let spec = build_substitution_spec_with_stack();
    assert_instantiate_app_lam_eq_surface(&spec);
}

#[test]
fn nat_and_bvar_helpers_are_constructive() {
    let spec = build_substitution_spec_with_stack();
    assert_nat_sub_surface(&spec);
    assert_instantiate_bvar_at_eq_surface(&spec);
}

#[test]
fn lift_zero_surface_is_constructive() {
    let spec = build_substitution_spec_with_stack();
    assert_lift_at_amount_zero_surface(&spec);
    assert_instantiate_bvar_zero_surface(&spec);
}
