// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R26 tests — the HeadFree port, the single-contractum rule, the bridge to an
//! induction hypothesis, and the two refusals that pin what each needs.

use super::super::candmodel_construct_r26_src::{
    probe_one_without_recenvclosed, probe_star_walker_with_cr1, r26_all_sources, r26_items,
    VAL_CANDEXPHF_BETA_SUBST, VAL_CANDHF_BETASTAR_CLOSED,
};
use super::*;
use crate::test_utils::parse_check;

/// Register R26 into a freshly-built substitution spec if the bundle stage has
/// not already done it.
fn r26_spec() -> Specification {
    let mut spec = crate::test_utils::build_substitution_spec_with_stack();
    if spec.definitions().contains_key("r26_candExpHF_beta_subst") {
        return spec;
    }
    spec.add_candmodel_construct_r26()
        .expect("R26 should register into the substitution spec");
    spec
}

/// Parse every generated source.
#[test]
fn test_candmodel_r26_sources_parse() {
    for (name, src) in r26_all_sources() {
        parse_check(&src).unwrap_or_else(|e| panic!("R26 source {name} does not parse: {e}"));
    }
    parse_check(&probe_star_walker_with_cr1()).expect("the cr1 probe must parse");
    parse_check(&probe_one_without_recenvclosed())
        .expect("the dropped-RecEnvClosed probe must parse");
}

/// No name registered twice, and the load-bearing ones are all present.
#[test]
fn test_candmodel_r26_names_are_unique() {
    let mut seen = std::collections::BTreeSet::new();
    for (name, _) in r26_all_sources() {
        assert!(seen.insert(name.clone()), "R26 registers {name} twice");
    }
    for required in [
        "r26_candHF_betaStar_closed",
        "r26_candExpHF_beta_subst",
        "r26_red_beta_expand_one",
        "r26_red_lam_one",
        "r26_lam_premise_is_the_induction_hypothesis",
    ] {
        assert!(seen.contains(required), "R26 lost {required}");
    }
}

/// ITERATION TOOL — reports EVERY failure in one message.
#[test]
fn test_candmodel_r26_scratch_elaborates() {
    let mut spec = crate::test_utils::build_substitution_spec_with_stack();
    // WIRED-STATE BRANCH, deliberately NOT an early `return`. A bare return is a
    // self-skip: once the rung is in `bundles.rs` this test would report ok
    // forever, including if the stage were later dropped. Assert the rung's whole
    // table is live in the built spec instead, so the wired path carries a claim.
    if spec.definitions().contains_key("r26_candExpHF_beta_subst") {
        for (name, _) in r26_all_sources() {
            assert!(
                spec.env()
                    .get_const(&clean_kernel::Name::from_string(&name))
                    .is_some(),
                "R26 is wired but {name} is absent from the built spec"
            );
        }
    } else {
        let mut failures: Vec<String> = Vec::new();
        for item in r26_items() {
            let R26Item::Thm { name, ty, val } = item;
            if let Err(e) = add_thm(&mut spec, &name, ty, val, &[], "r26 scratch") {
                failures.push(format!("THM {name}: {e}"));
            }
        }
        assert!(
            failures.is_empty(),
            "R26 registration failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
    }
}

/// Every R26 constant is registered and every theorem re-verifies.
#[test]
fn test_candmodel_r26_registered_and_reverifies() {
    let spec = r26_spec();
    for (name, _) in r26_all_sources() {
        assert!(
            spec.definitions().contains_key(&name)
                || spec
                    .env()
                    .get_const(&clean_kernel::Name::from_string(&name))
                    .is_some(),
            "R26 constant {name} is not registered"
        );
        spec.verify_definition(&name)
            .unwrap_or_else(|e| panic!("R26 theorem {name} does not re-verify: {e:?}"));
    }
}

/// CENSUS. The computed axiom closure must be empty for every R26 constant.
#[test]
fn test_candmodel_r26_axiom_closure_is_empty() {
    let spec = r26_spec();
    for (name, _) in r26_all_sources() {
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

/// CENSUS, by kernel ground truth, over the bundle R26 actually changes.
#[test]
fn test_candmodel_r26_admits_no_new_census_axiom() {
    let spec = r26_spec();
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
        "R26 newly admitted kernel axioms into the substitution bundle: {newly:?}"
    );
}

/// MEASUREMENT: the star walker really is the cr2 face and nothing else.
///
/// The module doc's whole justification for calling the port mechanical is that
/// R2's proof uses cr2, which is unrestricted in both candidate classes. Swap
/// cr2 for cr1 and the kernel must refuse: cr1 says members are `whnf_acc`,
/// which does not move membership along a step.
#[test]
fn test_candmodel_r26_star_walker_is_the_cr2_face() {
    let mut spec = r26_spec();
    assert!(
        spec.add_recursive_def(&probe_star_walker_with_cr1(), "cr2 control")
            .is_err(),
        "the star walker goes through with cr1 — the port's justification (that it is the cr2 \
         face, and cr2 is unrestricted) is wrong"
    );
}

/// MEASUREMENT: `RecEnvClosed` is carried, not free.
#[test]
fn test_candmodel_r26_carries_recenvclosed() {
    let mut spec = r26_spec();
    assert!(
        spec.add_recursive_def(&probe_one_without_recenvclosed(), "premise control")
            .is_err(),
        "the single-contractum rule goes through without RecEnvClosed — betaStar_inst_transport \
         does not need it after all, and the module doc's accounting is wrong"
    );
}

/// The port really is R2's proof with two names changed — measured against R2's
/// own source rather than asserted.
#[test]
fn test_candmodel_r26_is_r2s_proof_with_two_names_changed() {
    use super::super::candmodel_construct_r2 as r2;
    let ported = VAL_CANDHF_BETASTAR_CLOSED
        .replace("IsCandHF ", "IsCandSet ")
        .replace("isCandHF_cr2", "isCandSet_cr2");
    assert_eq!(
        ported,
        r2::VAL_CANDSET_BETASTAR_CLOSED,
        "r26_candHF_betaStar_closed is no longer R2's candSet_betaStar_closed with IsCandSet and \
         isCandSet_cr2 renamed — the port has acquired content of its own and the module doc's \
         claim that it is mechanical is wrong"
    );
    assert!(
        VAL_CANDEXPHF_BETA_SUBST.contains("candExpHF_beta")
            && VAL_CANDEXPHF_BETA_SUBST.contains("r26_candHF_betaStar_closed")
            && VAL_CANDEXPHF_BETA_SUBST.contains("betaStar_inst_transport"),
        "the single-contractum engine no longer goes through R5's engine, the star walker and the \
         transport"
    );
}

/// R25 named what its `lam` rule did not take.
#[test]
fn test_candmodel_r26_follows_r25() {
    let doc = crate::test_utils::flatten_module_doc(include_str!("candmodel_construct_r25.rs"));
    assert!(
        doc.contains("family-shaped premise"),
        "R25 no longer names the family-shaped premise — R26's premise has moved"
    );
}
