// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Fail-closed pins for the `infer_terminates` census-axiom retirement
//! (`infer_terminates_proof.rs`).
//!
//! The former SN-pillar census axiom `infer_terminates`
//! (`forall e, terminates_infer e`) must now be a real `DerivedProved` closed
//! term with an EMPTY non-foundational computed closure, its statement must be
//! UNCHANGED (exactly the axiom-as-stated), and it must no longer lower to a
//! kernel axiom. The support ladder (`childAcc`, `subexpr_step_acc_inv`) must
//! likewise be non-axiom and empty-debt, and the whole ladder must re-typecheck
//! against the live kernel environment.

use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec_axiom_closure::{computed_axiom_closure, foundational_rule_names};
use crate::Specification;

/// Build the substitution subset of the spec (the `add_infer_terminates_proof`
/// stage is in the Substitution bundle, right after
/// `add_whnf_terminates_well_typed`; see `bundles.rs`).
fn build_infer_terminates_test_spec() -> Specification {
    crate::test_utils::build_substitution_spec_with_stack()
}

/// The whole ladder registers.
#[test]
fn test_infer_terminates_ladder_registered() {
    let spec = build_infer_terminates_test_spec();
    for name in ["childAcc", "subexpr_step_acc_inv", "infer_terminates"] {
        assert!(
            spec.definitions().contains_key(name),
            "{name} should be registered by the add_infer_terminates_proof stage"
        );
    }
}

/// FAIL-CLOSED PIN: `infer_terminates` and its support lemma are genuine
/// non-axiom, DerivedProved closed terms (carry a proof value) with an EMPTY
/// declared axiom closure. `infer_terminates` in particular must have flipped
/// from `is_axiom: true` (HelperAxiom) to a proof.
#[test]
fn test_infer_terminates_derived_proved_zero_axiom_deps() {
    let spec = build_infer_terminates_test_spec();
    for name in ["subexpr_step_acc_inv", "infer_terminates"] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
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

/// STATEMENT-STABILITY + HONESTY PIN: the retired axiom's statement is UNCHANGED
/// (a proof of the axiom AS STATED, not a weakening/reword), and the description
/// carries the honest scope caveat (structural child recursion, NOT the WHNF
/// reductions on types).
#[test]
fn test_infer_terminates_statement_unchanged_and_honest() {
    let spec = build_infer_terminates_test_spec();
    let thm = spec
        .definitions()
        .get("infer_terminates")
        .expect("infer_terminates should be registered");
    assert_eq!(
        thm.type_src, "forall (e : KExpr), terminates_infer e",
        "the retired axiom's statement must be byte-identical to the axiom as stated"
    );
    assert!(
        thm.description.contains("STRUCTURAL")
            && thm.description.contains("whnf_terminates_well_typed")
            && thm
                .description
                .contains("NOT full infer-with-reduction termination"),
        "the description must carry the honest scope caveat (structural child recursion, \
         separate from the WHNF-reduction SN whnf_terminates_well_typed): {}",
        thm.description
    );
}

/// KERNEL-GROUND-TRUTH HONESTY PIN: the computed transitive axiom closure of the
/// retired theorem (and its inversion helper) rests ONLY on the spec's
/// self-declared FoundationalRule primitives — an empty residual, so
/// `DerivedProved` is not an overclaim.
#[test]
fn test_infer_terminates_computed_closure_is_foundational_only() {
    let spec = build_infer_terminates_test_spec();
    let foundational = foundational_rule_names(&spec);
    for name in ["subexpr_step_acc_inv", "infer_terminates"] {
        let closure = computed_axiom_closure(&spec, name);
        let debt: Vec<&String> = closure.difference(&foundational).collect();
        assert!(
            debt.is_empty(),
            "{name} must have an empty non-foundational computed closure, got: {debt:?}"
        );
    }
}

/// The theorems re-verify against the live kernel environment (the stored
/// elaborated proof terms type-check at their declared types) — the real witness
/// that the proof is kernel-checked, not merely spec-registered.
#[test]
fn test_infer_terminates_reverifies_in_kernel() {
    let spec = build_infer_terminates_test_spec();
    for name in ["childAcc", "subexpr_step_acc_inv", "infer_terminates"] {
        spec.verify_definition(name)
            .unwrap_or_else(|_| panic!("{name} should re-typecheck in the spec environment"));
    }
}
