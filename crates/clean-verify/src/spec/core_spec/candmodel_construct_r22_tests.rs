// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R22 tests — the star form, the native conversion lemma, the drift checks
//! that close R18's transported stack, and the two refusals.

use super::super::candmodel_construct_r22_src::{
    probe_conv_without_second_star, probe_star_refl, r22_all_sources, r22_items, VAL_XVAL_CONV,
};
use super::*;
use crate::test_utils::parse_check;

/// Register R22 into a freshly-built substitution spec if the bundle stage has
/// not already done it.
fn r22_spec() -> Specification {
    let mut spec = crate::test_utils::build_substitution_spec_with_stack();
    if spec.definitions().contains_key("r22_xval_conv") {
        return spec;
    }
    spec.add_candmodel_construct_r22()
        .expect("R22 should register into the substitution spec");
    spec
}

/// Parse every generated source.
#[test]
fn test_candmodel_r22_sources_parse() {
    for (name, src) in r22_all_sources() {
        parse_check(&src).unwrap_or_else(|e| panic!("R22 source {name} does not parse: {e}"));
    }
    parse_check(&probe_star_refl()).expect("the Eq.refl probe must parse");
    parse_check(&probe_conv_without_second_star()).expect("the dropped-premise probe must parse");
}

/// No name registered twice, and the load-bearing ones are all present.
#[test]
fn test_candmodel_r22_names_are_unique() {
    let mut seen = std::collections::BTreeSet::new();
    for (name, _) in r22_all_sources() {
        assert!(seen.insert(name.clone()), "R22 registers {name} twice");
    }
    for required in [
        "r22_xval_star_sem",
        "r22_xval_step_star",
        "r22_xval_conv",
        "r22_step_star_extends_transported",
        "r22_conv_extends_transported",
        "r22_step_star_reaches_let",
        "r22_conv_reaches_let",
    ] {
        assert!(seen.contains(required), "R22 lost {required}");
    }
}

/// ITERATION TOOL — reports EVERY failure in one message.
#[test]
fn test_candmodel_r22_scratch_elaborates() {
    let mut spec = crate::test_utils::build_substitution_spec_with_stack();
    // WIRED-STATE BRANCH, deliberately NOT an early `return`. A bare return is a
    // self-skip: once the rung is in `bundles.rs` this test would report ok
    // forever, including if the stage were later dropped. Assert the rung's whole
    // table is live in the built spec instead, so the wired path carries a claim.
    if spec.definitions().contains_key("r22_xval_conv") {
        for (name, _) in r22_all_sources() {
            assert!(
                spec.env()
                    .get_const(&clean_kernel::Name::from_string(&name))
                    .is_some(),
                "R22 is wired but {name} is absent from the built spec"
            );
        }
    } else {
        let mut failures: Vec<String> = Vec::new();
        for item in r22_items() {
            match item {
                R22Item::Def { name, src } => {
                    if let Err(e) = spec.add_recursive_def(&src, "r22 scratch") {
                        failures.push(format!("DEF {name}: {e}"));
                    }
                }
                R22Item::Thm { name, ty, val } => {
                    if let Err(e) = add_thm(&mut spec, &name, ty, val, &[], "r22 scratch") {
                        failures.push(format!("THM {name}: {e}"));
                    }
                }
            }
        }
        assert!(
            failures.is_empty(),
            "R22 registration failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
    }
}

/// Every R22 constant is registered and every theorem re-verifies.
#[test]
fn test_candmodel_r22_registered_and_reverifies() {
    let spec = r22_spec();
    for (name, _) in r22_all_sources() {
        assert!(
            spec.definitions().contains_key(&name)
                || spec
                    .env()
                    .get_const(&clean_kernel::Name::from_string(&name))
                    .is_some(),
            "R22 constant {name} is not registered"
        );
    }
    for item in r22_items() {
        if let R22Item::Thm { name, .. } = item {
            spec.verify_definition(&name)
                .unwrap_or_else(|e| panic!("R22 theorem {name} does not re-verify: {e:?}"));
        }
    }
}

/// CENSUS. The computed axiom closure must be empty for every R22 constant.
#[test]
fn test_candmodel_r22_axiom_closure_is_empty() {
    let spec = r22_spec();
    for (name, _) in r22_all_sources() {
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

/// CENSUS, by kernel ground truth, over the bundle R22 actually changes.
#[test]
fn test_candmodel_r22_admits_no_new_census_axiom() {
    let spec = r22_spec();
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
        "R22 newly admitted kernel axioms into the substitution bundle: {newly:?}"
    );
}

/// MEASUREMENT: the star law is NOT a definitional identity.
#[test]
fn test_candmodel_r22_star_is_not_definitional() {
    let mut spec = r22_spec();
    assert!(
        spec.add_recursive_def(&probe_star_refl(), "negative control")
            .is_err(),
        "the native star law is DEFINITIONAL — the whnfStar induction witnesses nothing"
    );
}

/// MEASUREMENT: conversion needs BOTH reduction premises.
///
/// With `whnfStar e2 w` dropped, `e1` and `e2` need share no reduct at all and
/// the statement would say arbitrary same-shaped terms have the same
/// inhabitants. The probe proves it by returning the membership unchanged; the
/// kernel must refuse. Without this, a reader could not tell conversion from a
/// coercion that never looks at the reducts.
#[test]
fn test_candmodel_r22_conversion_needs_both_reductions() {
    let mut spec = r22_spec();
    assert!(
        spec.add_recursive_def(&probe_conv_without_second_star(), "premise control")
            .is_err(),
        "conversion goes through with only ONE reduction premise — it is not comparing reducts"
    );
}

/// The conversion proof spends NO `PropBox` and NO irrelevance hypothesis, and
/// the module doc says so. Measured from the rung's OWN source, because both
/// claims are about what the proof does NOT contain and are therefore invisible
/// to every other test here.
#[test]
fn test_candmodel_r22_conv_needs_neither_box_nor_irrelevance() {
    assert!(
        !VAL_XVAL_CONV.contains("PropBox"),
        "r22_xval_conv now boxes its conclusion — the module doc's claim that a membership is \
         already a Type is wrong"
    );
    assert!(
        !VAL_XVAL_CONV.contains("irrel"),
        "r22_xval_conv now spends an irrelevance lemma — the module doc's claim that the star \
         form's own witness relates both sequences is wrong"
    );
    assert!(
        VAL_XVAL_CONV.contains("r22_xval_star_sem") && VAL_XVAL_CONV.contains("Eq.substType"),
        "r22_xval_conv no longer goes through the star form and the membership transport"
    );
}

/// R21 named this rung's subject.
#[test]
fn test_candmodel_r22_closes_the_item_r21_named() {
    let doc = crate::test_utils::flatten_module_doc(include_str!("candmodel_construct_r21.rs"));
    assert!(
        doc.contains("a `whnfStar` induction rather than a `WKC` one"),
        "R21 no longer names the whnfStar induction as its next item — R22's premise has moved"
    );
}
