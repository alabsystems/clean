// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_verify::spec::ProofStatus;
use clean_verify::Specification;

use super::{assert_exact_axiom_deps, build_substitution_spec_with_stack};

fn assert_instantiate_subst_commutes_eq_surface(spec: &Specification) {
    let subst_eq = spec
        .definitions()
        .get("instantiate_subst_commutes_eq")
        .expect("instantiate_subst_commutes_eq should exist");
    assert!(
        subst_eq.value_src.is_some(),
        "instantiate_subst_commutes_eq should have a proof term"
    );
    assert!(
        !subst_eq.is_axiom,
        "instantiate_subst_commutes_eq should not be an axiom"
    );
    assert!(
        !subst_eq.axiom_deps.contains("instantiate_at_nested_commutes_bvar"),
        "instantiate_subst_commutes_eq should flatten through the derived bvar theorem to leaf blockers"
    );
    assert_exact_axiom_deps(subst_eq, &[], "instantiate_subst_commutes_eq");
}

fn assert_nested_commutes_surface(spec: &Specification) {
    let nested_commutes = spec
        .definitions()
        .get("instantiate_at_nested_commutes")
        .expect("instantiate_at_nested_commutes should exist");
    assert!(
        nested_commutes.value_src.is_some(),
        "instantiate_at_nested_commutes should now have a structural proof term"
    );
    assert!(
        !nested_commutes.is_axiom,
        "instantiate_at_nested_commutes should no longer be a raw helper axiom"
    );
    assert_eq!(
        nested_commutes.proof_status,
        ProofStatus::DerivedProved,
        "instantiate_at_nested_commutes should be DerivedProved (subst_lift_interchange chain now constructive)"
    );
    assert_exact_axiom_deps(nested_commutes, &[], "instantiate_at_nested_commutes");
}

fn assert_zero_commutes_surface(spec: &Specification) {
    let zero_commutes = spec
        .definitions()
        .get("instantiate_at_zero_commutes")
        .expect("instantiate_at_zero_commutes should exist");
    assert!(
        zero_commutes.value_src.is_some(),
        "instantiate_at_zero_commutes should now be routed through the binder-aware nested theorem"
    );
    assert!(
        !zero_commutes.is_axiom,
        "instantiate_at_zero_commutes should no longer be a raw helper axiom"
    );
    assert_eq!(
        zero_commutes.proof_status,
        ProofStatus::DerivedProved,
        "instantiate_at_zero_commutes should be DerivedProved (subst_lift_interchange chain now constructive)"
    );
    assert_exact_axiom_deps(zero_commutes, &[], "instantiate_at_zero_commutes");
}

fn assert_instantiate_subst_commutes_surface(spec: &Specification) {
    assert_instantiate_subst_commutes_eq_surface(spec);
    assert_nested_commutes_surface(spec);
    assert_zero_commutes_surface(spec);
}

fn assert_lift_cancel_branch_surface(spec: &Specification) {
    for name in ["lift_cancel_gen_bvar_below", "lift_cancel_gen_bvar_above"] {
        let branch = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should exist"));
        assert!(
            branch.value_src.is_some(),
            "{name} should now have an explicit proof term"
        );
        assert!(
            !branch.is_axiom,
            "{name} should be constructive, not a helper axiom"
        );
        assert_eq!(
            branch.proof_status,
            ProofStatus::DerivedProved,
            "{name} should be fully constructive"
        );
        assert_exact_axiom_deps(branch, &[], name);
    }

    let above = spec
        .definitions()
        .get("lift_cancel_gen_bvar_above")
        .expect("lift_cancel_gen_bvar_above should exist");
    let above_deps = above
        .dependencies
        .as_ref()
        .expect("lift_cancel_gen_bvar_above should record its direct proof dependencies");
    assert!(
        above_deps.contains("nat_sub_zero_implies_sub_succ_zero"),
        "lift_cancel_gen_bvar_above should derive the shifted zero witness from nat_sub_zero_implies_sub_succ_zero"
    );
    assert!(
        !above
            .type_src
            .contains("Eq Nat (Nat.sub cutoff (Nat.add idx (Nat.succ Nat.zero))) Nat.zero ->"),
        "lift_cancel_gen_bvar_above should no longer require the shifted zero witness as an explicit hypothesis"
    );
}

fn assert_lift_cancel_wrapper_surface(spec: &Specification) {
    let lift_cancel = spec
        .definitions()
        .get("lift_cancel")
        .expect("lift_cancel should exist");
    assert!(
        lift_cancel.value_src.is_some(),
        "lift_cancel should now have a wrapper proof term"
    );
    assert!(
        !lift_cancel.is_axiom,
        "lift_cancel should no longer be tracked as a raw helper axiom"
    );
    assert_eq!(
        lift_cancel.proof_status,
        ProofStatus::DerivedProved,
        "lift_cancel should now be fully constructive via lift_cancel_gen"
    );
    assert_exact_axiom_deps(lift_cancel, &[], "lift_cancel");
}

fn assert_lift_cancel_gen_surface(spec: &Specification) {
    let lift_cancel_gen = spec
        .definitions()
        .get("lift_cancel_gen")
        .expect("lift_cancel_gen should exist");
    assert!(
        lift_cancel_gen.value_src.is_some(),
        "lift_cancel_gen should now have a proof term"
    );
    assert!(
        !lift_cancel_gen.is_axiom,
        "lift_cancel_gen should no longer be an axiom"
    );
    assert_eq!(
        lift_cancel_gen.proof_status,
        ProofStatus::DerivedProved,
        "lift_cancel_gen should now be fully constructive"
    );
    assert!(
        lift_cancel_gen.axiom_deps.is_empty(),
        "lift_cancel_gen should not retain helper blockers: {:?}",
        lift_cancel_gen.axiom_deps
    );
    let lift_cancel_gen_deps = lift_cancel_gen
        .dependencies
        .as_ref()
        .expect("lift_cancel_gen should record its direct proof dependencies");
    assert!(
        lift_cancel_gen_deps.contains("lift_cancel_gen_bvar"),
        "lift_cancel_gen should route its bvar branch through the constructive lift_cancel_gen_bvar shell"
    );
}

fn assert_instantiate_at_bvar_commutes_surface(spec: &Specification) {
    let bvar_commutes = spec
        .definitions()
        .get("instantiate_at_bvar_commutes")
        .expect("instantiate_at_bvar_commutes should exist");
    assert!(
        bvar_commutes.value_src.is_some(),
        "instantiate_at_bvar_commutes should now have a proof term"
    );
    assert!(
        !bvar_commutes.is_axiom,
        "instantiate_at_bvar_commutes should no longer be tracked as an axiom"
    );
    assert_eq!(
        bvar_commutes.proof_status,
        ProofStatus::DerivedProved,
        "instantiate_at_bvar_commutes should now be fully constructive"
    );
    assert_exact_axiom_deps(bvar_commutes, &[], "instantiate_at_bvar_commutes");
    let bvar_commutes_deps = bvar_commutes
        .dependencies
        .as_ref()
        .expect("instantiate_at_bvar_commutes should record its branch proof dependencies");
    assert!(
        bvar_commutes_deps.contains("instantiate_at_bvar_commutes_succ_succ"),
        "instantiate_at_bvar_commutes should route the i>=2 branch through instantiate_at_bvar_commutes_succ_succ"
    );
}

fn assert_lift_cancel_surface(spec: &Specification) {
    assert_lift_cancel_branch_surface(spec);
    assert_lift_cancel_wrapper_surface(spec);
    assert_lift_cancel_gen_surface(spec);
    assert_instantiate_at_bvar_commutes_surface(spec);
}

fn assert_beta_subst_surface(spec: &Specification) {
    let beta_subst = spec
        .definitions()
        .get("beta_subst_commutes")
        .expect("beta_subst_commutes should exist");
    assert!(
        beta_subst.value_src.is_some(),
        "beta_subst_commutes should have a proof term"
    );
    assert!(
        !beta_subst.is_axiom,
        "beta_subst_commutes should not be an axiom"
    );
    assert!(
        !beta_subst.axiom_deps.contains("DefEq.beta"),
        "beta_subst_commutes should not list FoundationalRule DefEq.beta in axiom_deps"
    );
    assert!(
        !beta_subst.axiom_deps.contains("instantiate_at_app"),
        "beta_subst_commutes should no longer treat instantiate_at_app as trusted"
    );
    assert!(
        !beta_subst.axiom_deps.contains("instantiate_at_lam"),
        "beta_subst_commutes should no longer treat instantiate_at_lam as trusted"
    );
    assert!(
        !beta_subst.axiom_deps.contains("instantiate_at_zero_commutes"),
        "beta_subst_commutes should flatten through instantiate_at_zero_commutes to the leaf blocker"
    );
    assert!(
        !beta_subst
            .axiom_deps
            .contains("instantiate_at_nested_commutes_bvar"),
        "beta_subst_commutes should flatten through the derived bvar theorem to leaf blockers"
    );
    assert_exact_axiom_deps(beta_subst, &[], "beta_subst_commutes");
}

fn assert_beta_subst_at_surface(spec: &Specification) {
    let beta_subst_at = spec
        .definitions()
        .get("beta_subst_commutes_at")
        .expect("beta_subst_commutes_at should exist");
    // The constructive proof term for beta_subst_commutes_at has landed (#2872):
    // the same-bundle forward-reference cycle with def_eq_respects_subst_at is
    // broken by staged registration — beta_subst_commutes_at is registered as a
    // type-only forward declaration, then its body (DefEq.beta transported
    // through def_eq_respects_subst_at) is spliced in and kernel-verified once
    // def_eq_respects_subst_at exists. The placeholder church_rosser_whnf is
    // discharged across the chain, so this lemma is now DerivedProved with an
    // empty helper-axiom closure.
    assert!(
        beta_subst_at.value_src.is_some(),
        "beta_subst_commutes_at should now carry the spliced constructive proof term"
    );
    assert!(
        !beta_subst_at.is_axiom,
        "beta_subst_commutes_at with value_src must not be an axiom"
    );
    assert_eq!(
        beta_subst_at.proof_status,
        ProofStatus::DerivedProved,
        "beta_subst_commutes_at should be DerivedProved once the proof term is spliced"
    );
    assert_exact_axiom_deps(beta_subst_at, &[], "beta_subst_commutes_at");
}

fn assert_beta_subst_commutes_surface(spec: &Specification) {
    assert_beta_subst_surface(spec);
    assert_beta_subst_at_surface(spec);
}

#[test]
fn instantiate_subst_commutes_surface_is_constructive() {
    let spec = build_substitution_spec_with_stack();
    assert_instantiate_subst_commutes_surface(&spec);
}

#[test]
fn lift_cancel_surface_is_constructive() {
    let spec = build_substitution_spec_with_stack();
    assert_lift_cancel_surface(&spec);
}

#[test]
fn beta_subst_commutes_surface_is_constructive() {
    let spec = build_substitution_spec_with_stack();
    assert_beta_subst_commutes_surface(&spec);
}
