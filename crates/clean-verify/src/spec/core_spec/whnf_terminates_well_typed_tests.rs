// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Fail-closed pins for the `whnf_terminates_well_typed` census-axiom retirement
//! (`whnf_terminates_well_typed.rs`).
//!
//! The former census axiom `whnf_terminates_well_typed`
//! (`has_type e T -> terminates_whnf e`) must now be a real `DerivedProved`
//! closed term with an EMPTY non-foundational computed closure, its statement
//! must be UNCHANGED (exactly the axiom-as-stated over the context-free
//! `has_type`), and it must no longer lower to a kernel axiom. The support ladder
//! (`typable_const_free`, the const-head-none lemmas, `beta_reduces_to_bd_cf`,
//! `whnf_step_to_bd_cf`) must likewise be `DerivedProved` and empty-debt.

use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec_axiom_closure::{computed_axiom_closure, foundational_rule_names};
use crate::Specification;

/// Build the substitution subset of the spec (the
/// `add_whnf_terminates_well_typed` stage is in the Substitution bundle, right
/// after `add_whnf_normalizes`; see `bundles.rs`).
fn build_wt_test_spec() -> Specification {
    crate::test_utils::build_substitution_spec_with_stack()
}

/// The whole ladder registers.
#[test]
fn test_whnf_terminates_ladder_registered() {
    let spec = build_wt_test_spec();
    for name in [
        "typable_const_free",
        "const_free_kapp_fn",
        "const_free_head_name_none",
        "const_free_head_const_name_none",
        "beta_reduces_to_bd_cf",
        "whnf_step_to_bd_cf",
        "whnf_terminates_well_typed",
    ] {
        assert!(
            spec.definitions().contains_key(name),
            "{name} should be registered by the whnf_terminates_well_typed stage"
        );
    }
}

/// FAIL-CLOSED PIN: every lemma in the ladder — including the retired census
/// axiom — is a genuine DerivedProved closed term (not an axiom, carries a proof
/// value) with an EMPTY declared axiom closure.
#[test]
fn test_whnf_terminates_all_derived_proved_zero_axiom_deps() {
    let spec = build_wt_test_spec();
    for name in [
        "typable_const_free",
        "const_free_kapp_fn",
        "const_free_head_name_none",
        "const_free_head_const_name_none",
        "beta_reduces_to_bd_cf",
        "whnf_step_to_bd_cf",
        "whnf_terminates_well_typed",
    ] {
        let def = spec.definitions().get(name).unwrap_or_else(|| {
            panic!("{name} should be registered by the whnf_terminates_well_typed stage")
        });
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

/// STATEMENT-STABILITY PIN: the retired axiom's statement is UNCHANGED — this is
/// a proof of the axiom AS STATED (over the context-free `has_type`), not a
/// weakening/reword. The honesty caveat (degenerate context-free fragment, NOT
/// full dependent-CIC SN) is documented in the description.
#[test]
fn test_whnf_terminates_statement_unchanged_and_honest() {
    let spec = build_wt_test_spec();
    let thm = spec
        .definitions()
        .get("whnf_terminates_well_typed")
        .expect("whnf_terminates_well_typed should be registered");
    assert_eq!(
        thm.type_src, "forall (e : KExpr) (T : KExpr), has_type e T -> terminates_whnf e",
        "the retired axiom's statement must be byte-identical to the axiom as stated"
    );
    assert!(
        thm.description.contains("DEGENERATE")
            && thm
                .description
                .contains("NOT a claim of full dependent-CIC SN"),
        "the description must carry the honesty caveat (degenerate context-free fragment, \
         not full dependent-CIC SN): {}",
        thm.description
    );
}

/// KERNEL-GROUND-TRUTH HONESTY PIN: the computed transitive axiom closure of the
/// retired theorem (and its ladder) rests ONLY on the spec's self-declared
/// FoundationalRule primitives — an empty residual, so `DerivedProved` is not an
/// overclaim.
#[test]
fn test_whnf_terminates_computed_closure_is_foundational_only() {
    let spec = build_wt_test_spec();
    let foundational = foundational_rule_names(&spec);
    for name in [
        "typable_const_free",
        "const_free_head_const_name_none",
        "beta_reduces_to_bd_cf",
        "whnf_step_to_bd_cf",
        "whnf_terminates_well_typed",
    ] {
        let closure = computed_axiom_closure(&spec, name);
        let debt: Vec<&String> = closure.difference(&foundational).collect();
        assert!(
            debt.is_empty(),
            "{name} must have an empty non-foundational computed closure, got: {debt:?}"
        );
    }
}

/// The theorems re-verify against the live kernel environment (the stored
/// elaborated proof terms type-check at their declared types) — the real
/// witness that the proof is kernel-checked, not merely spec-registered.
#[test]
fn test_whnf_terminates_reverifies_in_kernel() {
    let spec = build_wt_test_spec();
    for name in [
        "typable_const_free",
        "const_free_kapp_fn",
        "const_free_head_name_none",
        "const_free_head_const_name_none",
        "beta_reduces_to_bd_cf",
        "whnf_step_to_bd_cf",
        "whnf_terminates_well_typed",
    ] {
        spec.verify_definition(name)
            .unwrap_or_else(|_| panic!("{name} should re-typecheck in the spec environment"));
    }
}
