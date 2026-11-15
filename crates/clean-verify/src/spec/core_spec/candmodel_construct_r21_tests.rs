// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R21 tests — the native step law, the semantic lambda inversion it needed,
//! and the two refusals that measure what the statement actually says.

use super::super::candmodel_construct_r21_src::{
    probe_step_refl, probe_step_without_the_step, r21_all_sources, r21_items, val_xval_step_sem,
};
use super::*;
use crate::test_utils::parse_check;

/// Register R21 into a freshly-built substitution spec if the bundle stage has
/// not already done it.
fn r21_spec() -> Specification {
    let mut spec = crate::test_utils::build_substitution_spec_with_stack();
    if spec.definitions().contains_key("r21_xval_step") {
        return spec;
    }
    spec.add_candmodel_construct_r21()
        .expect("R21 should register into the substitution spec");
    spec
}

/// Parse every generated source. Microseconds, versus a whole spec build.
#[test]
fn test_candmodel_r21_sources_parse() {
    for (name, src) in r21_all_sources() {
        parse_check(&src).unwrap_or_else(|e| panic!("R21 source {name} does not parse: {e}"));
    }
    parse_check(&probe_step_refl()).expect("the Eq.refl probe must parse");
    parse_check(&probe_step_without_the_step()).expect("the dropped-premise probe must parse");
}

/// No name registered twice, and the load-bearing ones are all present.
#[test]
fn test_candmodel_r21_names_are_unique() {
    let mut seen = std::collections::BTreeSet::new();
    for (name, _) in r21_all_sources() {
        assert!(seen.insert(name.clone()), "R21 registers {name} twice");
    }
    for required in [
        "r21_xvalLamT",
        "r21_xval_lam_inv",
        "r21_xval_step_sem",
        "r21_xval_step",
        "r21_step_extends_transported",
        "r21_step_reaches_let",
    ] {
        assert!(seen.contains(required), "R21 lost {required}");
    }
}

/// ITERATION TOOL. Registers the whole table and reports EVERY failure in one
/// message instead of dying on the first — the R13-R20 pattern.
#[test]
fn test_candmodel_r21_scratch_elaborates() {
    let mut spec = crate::test_utils::build_substitution_spec_with_stack();
    // WIRED-STATE BRANCH, deliberately NOT an early `return`. A bare return is a
    // self-skip: once the rung is in `bundles.rs` this test would report ok
    // forever, including if the stage were later dropped. Assert the rung's whole
    // table is live in the built spec instead, so the wired path carries a claim.
    if spec.definitions().contains_key("r21_xval_step") {
        for (name, _) in r21_all_sources() {
            assert!(
                spec.env()
                    .get_const(&clean_kernel::Name::from_string(&name))
                    .is_some(),
                "R21 is wired but {name} is absent from the built spec"
            );
        }
    } else {
        let mut failures: Vec<String> = Vec::new();
        for item in r21_items() {
            match item {
                R21Item::Def { name, src } => {
                    if let Err(e) = spec.add_recursive_def(&src, "r21 scratch") {
                        failures.push(format!("DEF {name}: {e}"));
                    }
                }
                R21Item::Thm { name, ty, val } => {
                    if let Err(e) = add_thm(&mut spec, &name, ty, val, &[], "r21 scratch") {
                        failures.push(format!("THM {name}: {e}"));
                    }
                }
            }
        }
        assert!(
            failures.is_empty(),
            "R21 registration failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
    }
}

/// Every R21 constant is registered and every theorem re-verifies.
#[test]
fn test_candmodel_r21_registered_and_reverifies() {
    let spec = r21_spec();
    for (name, _) in r21_all_sources() {
        assert!(
            spec.definitions().contains_key(&name)
                || spec
                    .env()
                    .get_const(&clean_kernel::Name::from_string(&name))
                    .is_some(),
            "R21 constant {name} is not registered"
        );
    }
    for item in r21_items() {
        if let R21Item::Thm { name, .. } = item {
            spec.verify_definition(&name)
                .unwrap_or_else(|e| panic!("R21 theorem {name} does not re-verify: {e:?}"));
        }
    }
}

/// The computed inversion type and its proof must stay reducible — an
/// `add_definition` registration lowers to `Opaque`, and the step law's β case
/// reduces THROUGH `r21_xvalLamT` at every call.
#[test]
fn test_candmodel_r21_reduction_spine_delta_unfolds() {
    use clean_kernel::{ConstantKind, Name};
    let spec = r21_spec();
    for op in ["r21_xvalLamT", "r21_xval_lam_inv"] {
        let c = spec
            .env()
            .get_const(&Name::from_string(op))
            .unwrap_or_else(|| panic!("{op} missing from the R21 environment"));
        assert_eq!(
            c.kind,
            ConstantKind::Definition,
            "{op} must be a reducible Definition; Opaque stops the reduction the step law's beta \
             case depends on"
        );
    }
}

/// CENSUS. The computed axiom closure must be empty for every R21 constant.
#[test]
fn test_candmodel_r21_axiom_closure_is_empty() {
    let spec = r21_spec();
    for (name, _) in r21_all_sources() {
        let closure = crate::spec_axiom_closure::computed_axiom_closure(&spec, &name);
        assert!(
            closure.is_empty(),
            "{name} rests on non-foundational axioms: {closure:?}"
        );
        let markers = crate::spec_axiom_closure::computed_trust_markers(&spec, &name);
        assert!(
            markers.is_empty(),
            "{name} reaches a trust marker: {markers:?}"
        );
    }
}

/// CENSUS, by kernel ground truth, over the bundle R21 actually changes.
#[test]
fn test_candmodel_r21_admits_no_new_census_axiom() {
    let spec = r21_spec();
    const GOLDEN_JSON: &str = include_str!("../../../../../data/clean_verify_axiom_ratchet.json");
    let golden: std::collections::BTreeSet<String> = {
        let v: serde_json::Value =
            serde_json::from_str(GOLDEN_JSON).expect("axiom ratchet golden must parse");
        v["axioms"]
            .as_array()
            .expect("golden has an `axioms` array")
            .iter()
            .filter_map(|e| e["name"].as_str().map(str::to_string))
            .collect()
    };
    let live: Vec<String> = crate::axiom_ratchet::live_env_axioms(&spec)
        .into_iter()
        .map(|a| a.name)
        .collect();
    let newly = crate::axiom_ratchet::newly_admitted_axioms(&live, &golden);
    assert!(
        newly.is_empty(),
        "R21 newly admitted kernel axioms into the substitution bundle: {newly:?}"
    );
}

/// MEASUREMENT: the step law is NOT a definitional identity.
#[test]
fn test_candmodel_r21_step_is_not_definitional() {
    let mut spec = r21_spec();
    assert!(
        spec.add_recursive_def(&probe_step_refl(), "negative control")
            .is_err(),
        "the native step law is DEFINITIONAL — the seven-arm induction witnesses nothing"
    );
}

/// MEASUREMENT: the `whnf_step` premise is LOAD-BEARING.
///
/// Dropped, the statement would equate the interpretations of two arbitrary
/// terms of one shape, and the obvious proof attempt — `r17_xval_irrel`, which
/// equates two derivations of ONE judgment — does not typecheck, the two
/// derivations being at different terms. The kernel must refuse. Without this,
/// a reader could not tell the step law from derivation irrelevance.
#[test]
fn test_candmodel_r21_step_premise_is_load_bearing() {
    let mut spec = r21_spec();
    assert!(
        spec.add_recursive_def(&probe_step_without_the_step(), "premise control")
            .is_err(),
        "the step law's conclusion follows without its whnf_step premise — it is derivation \
         irrelevance wearing a step, not a step law"
    );
}

/// The induction reuses R13/R14's value congruences and R20's cast lemma, and
/// introduces no new semantic machinery beyond the lambda inversion. Measured
/// from the rung's OWN source.
#[test]
fn test_candmodel_r21_reuses_the_stack_below_it() {
    let src = val_xval_step_sem();
    for required in [
        "WKC.rec",
        "r15_whnf_stepT_inv",
        "letRedex_whnf_inv",
        "r20_xval_cast_term",
        "r20_xval_inst",
        "r21_xval_lam_inv",
        "r17_const_no_step",
        "r14_sval_pi_congr",
        "r14_vapply_congr",
        "r13_vd_arr_funext",
    ] {
        assert!(
            src.contains(required),
            "the native step induction no longer goes through {required}"
        );
    }
    for banned in ["sorry", "Classical", "axiom", "candInterp"] {
        assert!(
            !src.contains(banned),
            "the native step induction reaches {banned}, which no arm of it may"
        );
    }
}

/// R20 named this rung's subject.
#[test]
fn test_candmodel_r21_closes_the_item_r20_named() {
    let doc = crate::test_utils::flatten_module_doc(include_str!("candmodel_construct_r20.rs"));
    assert!(
        doc.contains("`val_step` by induction on `WKC`"),
        "R20 no longer names the native step law as its next item — R21's premise has moved"
    );
}
