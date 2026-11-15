// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R27 tests — the two RedAt-level facts, and the refusal that pins the
//! neutrality premise `r27_red_var` rests on.

use super::super::candmodel_construct_r27_src::{
    probe_lam_is_reducible, probe_var_without_env, r27_all_sources, r27_items, val_red_var,
};
use super::*;
use crate::test_utils::parse_check;

fn r27_spec() -> Specification {
    let mut spec = crate::test_utils::build_substitution_spec_with_stack();
    if spec.definitions().contains_key("r27_red_var") {
        return spec;
    }
    spec.add_candmodel_construct_r27()
        .expect("R27 should register into the substitution spec");
    spec
}

#[test]
fn test_candmodel_r27_sources_parse() {
    for (name, src) in r27_all_sources() {
        parse_check(&src).unwrap_or_else(|e| panic!("R27 source {name} does not parse: {e}"));
    }
    parse_check(&probe_lam_is_reducible()).expect("the lam probe must parse");
    parse_check(&probe_var_without_env()).expect("the dropped-env probe must parse");
}

#[test]
fn test_candmodel_r27_names_are_unique() {
    let mut seen = std::collections::BTreeSet::new();
    for (name, _) in r27_all_sources() {
        assert!(seen.insert(name.clone()), "R27 registers {name} twice");
    }
    for required in ["r27_red_irrel", "r27_red_var", "r27_red_var_is_sn"] {
        assert!(seen.contains(required), "R27 lost {required}");
    }
}

/// ITERATION TOOL — reports EVERY failure in one message.
#[test]
fn test_candmodel_r27_scratch_elaborates() {
    let mut spec = crate::test_utils::build_substitution_spec_with_stack();
    // WIRED-STATE BRANCH, deliberately NOT an early `return`. A bare return is a
    // self-skip: once the rung is in `bundles.rs` this test would report ok
    // forever, including if the stage were later dropped. Assert the rung's whole
    // table is live in the built spec instead, so the wired path carries a claim.
    if spec.definitions().contains_key("r27_red_var") {
        for (name, _) in r27_all_sources() {
            assert!(
                spec.env()
                    .get_const(&clean_kernel::Name::from_string(&name))
                    .is_some(),
                "R27 is wired but {name} is absent from the built spec"
            );
        }
    } else {
        let mut failures: Vec<String> = Vec::new();
        for item in r27_items() {
            let R27Item::Thm { name, ty, val } = item;
            if let Err(e) = add_thm(&mut spec, &name, ty, val, &[], "r27 scratch") {
                failures.push(format!("THM {name}: {e}"));
            }
        }
        assert!(
            failures.is_empty(),
            "R27 registration failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
    }
}

#[test]
fn test_candmodel_r27_registered_and_reverifies() {
    let spec = r27_spec();
    for (name, _) in r27_all_sources() {
        assert!(
            spec.definitions().contains_key(&name)
                || spec
                    .env()
                    .get_const(&clean_kernel::Name::from_string(&name))
                    .is_some(),
            "R27 constant {name} is not registered"
        );
        spec.verify_definition(&name)
            .unwrap_or_else(|e| panic!("R27 theorem {name} does not re-verify: {e:?}"));
    }
}

#[test]
fn test_candmodel_r27_axiom_closure_is_empty() {
    let spec = r27_spec();
    for (name, _) in r27_all_sources() {
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

#[test]
fn test_candmodel_r27_admits_no_new_census_axiom() {
    let spec = r27_spec();
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
        "R27 newly admitted kernel axioms into the substitution bundle: {newly:?}"
    );
}

/// THE SHARPEST CONTROL THIS RUNG CARRIES.
///
/// `r27_red_var` rests on `bvar` being NEUTRAL. The identical cr3 route at a
/// LAMBDA must be refused: the spec's `Neutral` sends a `lam` to `Empty`, so
/// `ConstFreeUnit.triv` cannot discharge the neutrality premise. If this ever
/// passed, `r24_RedAt` would be total — every term reducible at every type —
/// and every membership result in R18-R26 would be worthless.
#[test]
fn test_candmodel_r27_neutrality_is_load_bearing() {
    let mut spec = r27_spec();
    assert!(
        spec.add_recursive_def(&probe_lam_is_reducible(), "neutrality control")
            .is_err(),
        "a LAMBDA is reducible by the same cr3 route — Neutral does not discriminate, r24_RedAt \
         is total, and every membership result in this ladder is worthless"
    );
}

/// MEASUREMENT: candidacy still needs a good valuation.
#[test]
fn test_candmodel_r27_var_needs_a_good_valuation() {
    let mut spec = r27_spec();
    assert!(
        spec.add_recursive_def(&probe_var_without_env(), "premise control")
            .is_err(),
        "variables are reducible without GoodEnvD — R23's adequacy premise is decoration"
    );
}

/// The variable lemma goes through cr3 and the step inversion, and nothing else.
#[test]
fn test_candmodel_r27_var_uses_cr3_and_the_step_inversion() {
    let src = val_red_var();
    for required in ["isCandHF_cr3", "r15_whnf_stepT_inv", "ConstFreeUnit.triv"] {
        assert!(
            src.contains(required),
            "r27_red_var no longer goes through {required}"
        );
    }
    for banned in ["sorry", "Classical", "axiom", "KExpr.lam", "KExpr.let_"] {
        assert!(
            !src.contains(banned),
            "r27_red_var reaches {banned}, which it may not"
        );
    }
}

/// R26 named what remained after it.
#[test]
fn test_candmodel_r27_follows_r26() {
    let doc = crate::test_utils::flatten_module_doc(include_str!("candmodel_construct_r26.rs"));
    assert!(
        doc.contains("WHAT REMAINS IS THE JUDGMENT, NOT A LEMMA")
            || doc.contains("What remains is the JUDGMENT, not a lemma"),
        "R26 no longer names the judgment as what remains — R27's premise has moved"
    );
}
