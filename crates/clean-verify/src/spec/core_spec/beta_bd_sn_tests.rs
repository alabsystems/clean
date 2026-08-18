// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Fail-closed pins for the `beta_reduces_bd` strong-normalization ladder
//! (the kernel-checked port of `proofs/lean-aristotle/beta_sn_kexpr.lean`).
//!
//! Every ladder lemma must be a real `DerivedProved` closed term with an
//! EMPTY declared axiom closure, the final theorems must target EXACTLY the
//! iota-free relation `beta_reduces_bd` (never the full `beta_reduces`, whose
//! env-dependent iota arm makes the size argument false), and the computed
//! kernel-ground-truth closure of the whole ladder must rest on the
//! foundational-rule base only.

use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec_axiom_closure::{computed_axiom_closure, foundational_rule_names};
use crate::Specification;

/// Build the substitution subset of the spec (the `add_beta_bd_sn` stage is
/// in the Substitution bundle; see `bundles.rs`).
fn build_sn_test_spec() -> Specification {
    crate::test_utils::build_substitution_spec_with_stack()
}

/// The full ladder, bottom-up. Each entry must be DerivedProved with a closed
/// proof term and empty declared axiom_deps.
const LADDER: &[&str] = &[
    "nat_add_zero_zero",
    "lt_add_right_mono",
    "lt_add_left_mono",
    "ceil_zero_unbox",
    "typable_ceil_zero_box",
    "typable_bvar_ceiling_zero",
    "inst_id_of_ceiling_zero",
    "beta_bd_step_preserves_ceiling_zero",
    "beta_bd_step_decreases_size",
    "beta_bd_acc_of_ceiling_zero",
    "beta_bd_sn_well_typed",
    "beta_bd_sn_has_type",
];

/// The two inductives (the accessibility predicate and the Prop-in-Type box)
/// register with constructor + recursor surfaces.
#[test]
fn test_beta_bd_sn_inductives_registered() {
    let spec = build_sn_test_spec();
    for name in [
        "beta_bd_acc",
        "beta_bd_acc.intro",
        "beta_bd_acc.rec",
        "CeilZeroBox",
        "CeilZeroBox.mk",
        "CeilZeroBox.rec",
    ] {
        assert!(
            spec.definitions().contains_key(name),
            "{name} should be registered by the beta_bd_sn stage"
        );
    }
}

/// FAIL-CLOSED PIN: every ladder lemma is a genuine DerivedProved closed term
/// (not an axiom, carries a proof value) with an EMPTY declared axiom closure.
#[test]
fn test_beta_bd_sn_ladder_all_derived_proved_zero_axiom_deps() {
    let spec = build_sn_test_spec();
    for name in LADDER {
        let def = spec
            .definitions()
            .get(*name)
            .unwrap_or_else(|| panic!("{name} should be registered by the beta_bd_sn stage"));
        assert!(!def.is_axiom, "{name} must not be an axiom");
        assert_eq!(
            def.category,
            AxiomCategory::DerivedLemma,
            "{name} must be a DerivedLemma"
        );
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name} must be DerivedProved (closed, kernel-checked term)"
        );
        assert!(
            def.value_src.is_some(),
            "{name} must carry a closed proof term"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "{name} must declare an empty axiom closure (FOUNDATIONAL only): {:?}",
            def.axiom_deps
        );
    }
}

/// HONESTY PIN: the theorems target EXACTLY the iota-free `beta_reduces_bd`.
/// The final statement is SN over `beta_bd_acc` (accessibility under
/// `beta_reduces_bd`), and both the step lemma and the final theorem
/// descriptions must name the iota-free relation and disclaim the undischarged
/// census axiom (the delta/iota legs of `whnf_step`).
#[test]
fn test_beta_bd_sn_targets_exact_iota_free_relation() {
    let spec = build_sn_test_spec();

    let decrease = spec
        .definitions()
        .get("beta_bd_step_decreases_size")
        .expect("beta_bd_step_decreases_size should be registered");
    assert!(
        decrease.type_src.contains("beta_reduces_bd e e' ->")
            && decrease
                .type_src
                .contains("Lt (expr_size e') (expr_size e)"),
        "step-decrease must be stated over beta_reduces_bd and expr_size: {}",
        decrease.type_src
    );
    assert!(
        decrease.description.contains("beta_reduces_bd")
            && decrease
                .description
                .contains("FALSE for the full beta_reduces"),
        "step-decrease description must name the exact relation and the iota caveat: {}",
        decrease.description
    );

    let sn = spec
        .definitions()
        .get("beta_bd_sn_well_typed")
        .expect("beta_bd_sn_well_typed should be registered");
    assert_eq!(
        sn.type_src, "forall (e : KExpr) (T : KExpr), Typing e T -> beta_bd_acc e",
        "the goal theorem statement must be exactly SN of beta_reduces_bd for Typing"
    );
    assert!(
        sn.description.contains("beta_reduces_bd")
            && sn.description.contains("whnf_terminates_well_typed"),
        "the goal description must name beta_reduces_bd and the undischarged census axiom: {}",
        sn.description
    );

    // beta_bd_acc must quantify steps by beta_reduces_bd (pin the constructor
    // surface registered from the inductive source).
    let intro = spec
        .definitions()
        .get("beta_bd_acc.intro")
        .expect("beta_bd_acc.intro should be registered");
    assert!(
        intro.elaborated_type.is_some(),
        "beta_bd_acc.intro should carry its elaborated constructor type"
    );

    let has_type_form = spec
        .definitions()
        .get("beta_bd_sn_has_type")
        .expect("beta_bd_sn_has_type should be registered");
    assert_eq!(
        has_type_form.type_src, "forall (e : KExpr) (T : KExpr), has_type e T -> beta_bd_acc e",
        "the has_type phrasing must mirror the census axiom's statement shape"
    );
}

/// KERNEL-GROUND-TRUTH HONESTY PIN: the computed transitive axiom closure of
/// the ladder's load-bearing lemmas contains ONLY the spec's self-declared
/// FoundationalRule modeling primitives (Typing/DefEq/Eq.* rules) — the
/// residual DEBT is empty, so `DerivedProved` is not an overclaim. This is the
/// same partition the global `spec_axiom_closure_honesty` gate enforces,
/// pinned locally per-lemma so a regression names the exact culprit.
#[test]
fn test_beta_bd_sn_computed_closure_is_foundational_only() {
    let spec = build_sn_test_spec();
    let foundational = foundational_rule_names(&spec);
    for name in [
        "typable_bvar_ceiling_zero",
        "inst_id_of_ceiling_zero",
        "beta_bd_step_preserves_ceiling_zero",
        "beta_bd_step_decreases_size",
        "beta_bd_acc_of_ceiling_zero",
        "beta_bd_sn_well_typed",
        "beta_bd_sn_has_type",
    ] {
        let closure = computed_axiom_closure(&spec, name);
        let debt: Vec<&String> = closure.difference(&foundational).collect();
        assert!(
            debt.is_empty(),
            "{name} must have an empty non-foundational computed closure, got: {debt:?}"
        );
    }
}

/// The goal theorem re-verifies against the live kernel environment (the
/// stored elaborated proof term type-checks at its declared type).
#[test]
fn test_beta_bd_sn_goal_reverifies_in_kernel() {
    let spec = build_sn_test_spec();
    spec.verify_definition("beta_bd_sn_well_typed")
        .expect("beta_bd_sn_well_typed should re-typecheck in the spec environment");
    spec.verify_definition("beta_bd_step_decreases_size")
        .expect("beta_bd_step_decreases_size should re-typecheck in the spec environment");
}
