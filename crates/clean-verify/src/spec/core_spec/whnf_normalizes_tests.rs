// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Fail-closed pins for the MODEL-side WHNF normalization brick
//! (`whnf_normalizes.rs`, Front-2 recursive-grounding T3).
//!
//! The theorem `whnf_normalizes_bd` must be a real `DerivedProved` closed term
//! with an EMPTY non-foundational computed closure, its statement must target
//! EXACTLY the `has_type` const-free fragment and conclude a
//! `whnf_normalizes_result` (reduction to a beta_reduces_bd NORMAL FORM), and
//! the closure's normal-form base must be the honest WHNF-OR-STUCK predicate
//! `beta_bd_normal` (is_whnf OR whnf_stuck_head), NOT a bare is_whnf.

use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec_axiom_closure::{computed_axiom_closure, foundational_rule_names};
use crate::Specification;

/// Build the substitution subset of the spec (the `add_whnf_normalizes` stage is
/// in the Substitution bundle, right after `add_whnf_progress`; see
/// `bundles.rs`).
fn build_normalizes_test_spec() -> Specification {
    crate::test_utils::build_substitution_spec_with_stack()
}

/// DIAGNOSTIC (temporary): dump the recursor types so the fixedIndicesToParams
/// promotion shape (explicit vs implicit promoted param, motive arity) is known
/// exactly before writing the elimination terms.
#[test]
fn diagnostic_dump_recursor_types() {
    let spec = build_normalizes_test_spec();
    for name in [
        "whnf_normalizes_result.rec",
        "beta_bd_to.rec",
        "beta_bd_normal.rec",
        "beta_bd_acc.rec",
        "whnf_progress_result.rec",
    ] {
        let kname = clean_kernel::Name::from_string(name);
        match spec.env().get_const(&kname) {
            Some(ci) => println!("RECDUMP {name} :: {}", ci.type_),
            None => println!("RECDUMP {name} :: <ABSENT>"),
        }
    }
}

/// The closure/normal-form/witness inductives register with constructor +
/// recursor surfaces.
#[test]
fn test_whnf_normalizes_inductives_registered() {
    let spec = build_normalizes_test_spec();
    for name in [
        "beta_bd_normal",
        "beta_bd_normal.whnf",
        "beta_bd_normal.stuck",
        "beta_bd_normal.rec",
        "beta_bd_to",
        "beta_bd_to.refl",
        "beta_bd_to.step",
        "beta_bd_to.rec",
        "whnf_normalizes_result",
        "whnf_normalizes_result.intro",
        "whnf_normalizes_result.rec",
        "const_free_preserved_bd",
        "whnf_normalizes_prepend",
    ] {
        assert!(
            spec.definitions().contains_key(name),
            "{name} should be registered by the whnf_normalizes stage"
        );
    }
}

/// FAIL-CLOSED PIN: every lemma in the brick is a genuine DerivedProved closed
/// term (not an axiom, carries a proof value) with an EMPTY declared axiom
/// closure.
#[test]
fn test_whnf_normalizes_all_derived_proved_zero_axiom_deps() {
    let spec = build_normalizes_test_spec();
    for name in [
        "const_free_preserved_bd",
        "whnf_normalizes_prepend",
        "whnf_normalizes_bd",
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered by the whnf_normalizes stage"));
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

/// HONESTY PIN: the T3 theorem targets EXACTLY the has_type const-free fragment
/// and concludes a `whnf_normalizes_result` (reduction to a normal form), and
/// its description names the WHNF-OR-STUCK conclusion (not a bare is_whnf).
#[test]
fn test_whnf_normalizes_bd_targets_exact_fragment_and_conclusion() {
    let spec = build_normalizes_test_spec();

    let thm = spec
        .definitions()
        .get("whnf_normalizes_bd")
        .expect("whnf_normalizes_bd should be registered");
    assert_eq!(
        thm.type_src,
        "forall (e : KExpr) (T : KExpr), has_type e T -> const_free e -> \
         whnf_normalizes_result e",
        "the statement must be exactly has_type + const_free -> whnf_normalizes_result"
    );
    assert!(
        thm.description.contains("WHNF-OR-STUCK")
            && thm.description.contains("beta_reduces_bd")
            && thm.description.contains("normal form"),
        "the description must name the iota-free relation and the WHNF-or-stuck normal \
         form conclusion: {}",
        thm.description
    );

    // The closure's refl base must be beta_bd_normal, which carries BOTH the
    // is_whnf (whnf) and the whnf_stuck_head (stuck) constructors — the honest
    // WHNF-OR-STUCK normal form, not a bare is_whnf.
    let refl = spec
        .definitions()
        .get("beta_bd_to.refl")
        .expect("beta_bd_to.refl should be registered");
    let refl_ty = refl
        .elaborated_type
        .as_ref()
        .map(ToString::to_string)
        .unwrap_or_default();
    assert!(
        refl_ty.contains("beta_bd_normal"),
        "the closure refl base must be a beta_bd_normal normal form: {refl_ty}"
    );
    for ctor in ["beta_bd_normal.whnf", "beta_bd_normal.stuck"] {
        assert!(
            spec.definitions().contains_key(ctor),
            "{ctor} must be present so the normal form is honestly WHNF-OR-STUCK"
        );
    }
}

/// HONESTY PIN: the existential witness is over the stuck-aware closure
/// `beta_bd_to` and never over the landed `whnf_to` (whose refl bakes in
/// is_whnf only and cannot terminate on stuck normal forms).
#[test]
fn test_whnf_normalizes_result_over_stuck_aware_closure() {
    let spec = build_normalizes_test_spec();
    let intro = spec
        .definitions()
        .get("whnf_normalizes_result.intro")
        .expect("whnf_normalizes_result.intro should be registered");
    let intro_ty = intro
        .elaborated_type
        .as_ref()
        .map(ToString::to_string)
        .unwrap_or_default();
    assert!(
        intro_ty.contains("beta_bd_to"),
        "the witness must package a beta_bd_to reduction (stuck-aware closure): {intro_ty}"
    );
}

/// KERNEL-GROUND-TRUTH HONESTY PIN: the computed transitive axiom closure of
/// every brick lemma rests ONLY on the spec's self-declared FoundationalRule
/// primitives — an empty residual, so `DerivedProved` is not an overclaim. In
/// `const_whnf` is a semireducible Definition, not a helper axiom; in particular
/// the composition must not classify it, `delta_reduces`, or `iota_reduces` as
/// non-foundational axiom dependencies.
#[test]
fn test_whnf_normalizes_computed_closure_is_foundational_only() {
    let spec = build_normalizes_test_spec();
    assert!(
        !spec
            .definitions()
            .get("const_whnf")
            .expect("const_whnf should be registered")
            .is_axiom,
        "const_whnf must remain a Definition, not regress to a helper axiom"
    );
    let foundational = foundational_rule_names(&spec);
    for name in [
        "const_free_preserved_bd",
        "whnf_normalizes_prepend",
        "whnf_normalizes_bd",
    ] {
        let closure = computed_axiom_closure(&spec, name);
        let debt: Vec<&String> = closure.difference(&foundational).collect();
        assert!(
            debt.is_empty(),
            "{name} must have an empty non-foundational computed closure, got: {debt:?}"
        );
        assert!(
            !closure.contains("const_whnf"),
            "{name} must not classify const_whnf as an axiom dependency"
        );
        assert!(
            !closure.contains("delta_reduces") && !closure.contains("iota_reduces"),
            "{name} must not reach delta_reduces / iota_reduces"
        );
    }
}

/// The theorems re-verify against the live kernel environment (the stored
/// elaborated proof terms type-check at their declared types).
#[test]
fn test_whnf_normalizes_bd_reverifies_in_kernel() {
    let spec = build_normalizes_test_spec();
    for name in [
        "const_free_preserved_bd",
        "whnf_normalizes_prepend",
        "whnf_normalizes_bd",
    ] {
        spec.verify_definition(name)
            .unwrap_or_else(|_| panic!("{name} should re-typecheck in the spec environment"));
    }
}
