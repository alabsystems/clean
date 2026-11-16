// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R23 tests — adequacy, normalization, the two edges that keep it from being
//! vacuous, and the computed scope fact with its control.

use super::super::candmodel_construct_r23_src::{
    probe_good_without_env, probe_vcar_ty_collapses, r23_all_sources, r23_items, val_xval_good,
};
use super::*;
use crate::test_utils::parse_check;

/// Register R23 into a freshly-built substitution spec if the bundle stage has
/// not already done it.
fn r23_spec() -> Specification {
    let mut spec = crate::test_utils::build_substitution_spec_with_stack();
    if spec.definitions().contains_key("r23_xval_good") {
        return spec;
    }
    spec.add_candmodel_construct_r23()
        .expect("R23 should register into the substitution spec");
    spec
}

/// Parse every generated source.
#[test]
fn test_candmodel_r23_sources_parse() {
    for (name, src) in r23_all_sources() {
        parse_check(&src).unwrap_or_else(|e| panic!("R23 source {name} does not parse: {e}"));
    }
    parse_check(&probe_good_without_env()).expect("the dropped-env probe must parse");
    parse_check(&probe_vcar_ty_collapses()).expect("the vcarD collapse probe must parse");
}

/// No name registered twice, and the load-bearing ones are all present.
#[test]
fn test_candmodel_r23_names_are_unique() {
    let mut seen = std::collections::BTreeSet::new();
    for (name, _) in r23_all_sources() {
        assert!(seen.insert(name.clone()), "R23 registers {name} twice");
    }
    for required in [
        "r23_xval_good",
        "r23_isCandHI_xval",
        "r23_xval_members_sn",
        "r23_xval_excludes_omega",
        "r23_good_reproves_sval_good",
        "r23_sn_fires_at_konst",
        "r23_omega_excluded_at_konst",
        "r23_omega_excluded_at_let",
        "r23_vcar_arr_is_top",
        "r23_vcar_ty_is_the_set",
    ] {
        assert!(seen.contains(required), "R23 lost {required}");
    }
}

/// ITERATION TOOL — reports EVERY failure in one message.
#[test]
fn test_candmodel_r23_scratch_elaborates() {
    let mut spec = crate::test_utils::build_substitution_spec_with_stack();
    // WIRED-STATE BRANCH, deliberately NOT an early `return`. A bare return is a
    // self-skip: once the rung is in `bundles.rs` this test would report ok
    // forever, including if the stage were later dropped. Assert the rung's whole
    // table is live in the built spec instead, so the wired path carries a claim.
    if spec.definitions().contains_key("r23_xval_good") {
        for (name, _) in r23_all_sources() {
            assert!(
                spec.env()
                    .get_const(&clean_kernel::Name::from_string(&name))
                    .is_some(),
                "R23 is wired but {name} is absent from the built spec"
            );
        }
    } else {
        let mut failures: Vec<String> = Vec::new();
        for item in r23_items() {
            let R23Item::Thm { name, ty, val } = item;
            if let Err(e) = add_thm(&mut spec, &name, ty, val, &[], "r23 scratch") {
                failures.push(format!("THM {name}: {e}"));
            }
        }
        assert!(
            failures.is_empty(),
            "R23 registration failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
    }
}

/// Every R23 constant is registered and every theorem re-verifies.
#[test]
fn test_candmodel_r23_registered_and_reverifies() {
    let spec = r23_spec();
    for (name, _) in r23_all_sources() {
        assert!(
            spec.definitions().contains_key(&name)
                || spec
                    .env()
                    .get_const(&clean_kernel::Name::from_string(&name))
                    .is_some(),
            "R23 constant {name} is not registered"
        );
        spec.verify_definition(&name)
            .unwrap_or_else(|e| panic!("R23 theorem {name} does not re-verify: {e:?}"));
    }
}

/// CENSUS. The computed axiom closure must be empty for every R23 constant —
/// including the normalization theorem, which is the one a reader is most
/// likely to suspect of resting on something.
#[test]
fn test_candmodel_r23_axiom_closure_is_empty() {
    let spec = r23_spec();
    for (name, _) in r23_all_sources() {
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

/// CENSUS, by kernel ground truth, over the bundle R23 actually changes.
#[test]
fn test_candmodel_r23_admits_no_new_census_axiom() {
    let spec = r23_spec();
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
        "R23 newly admitted kernel axioms into the substitution bundle: {newly:?}"
    );
}

/// MEASUREMENT: the `GoodEnvD` premise is load-bearing.
///
/// Adequacy's `var` arm IS that premise applied at an index — a valuation's
/// entries need not be good otherwise — so a proof that drops it must be
/// refused. Without this, "every interpretation is good" could be read as
/// unconditional, which it is not.
#[test]
fn test_candmodel_r23_good_needs_a_good_valuation() {
    let mut spec = r23_spec();
    assert!(
        spec.add_recursive_def(&probe_good_without_env(), "premise control")
            .is_err(),
        "adequacy goes through without GoodEnvD — every valuation is good, and the premise on \
         every theorem in this rung is decoration"
    );
}

/// MEASUREMENT: `vcarD` does NOT collapse at `ty`.
///
/// `r23_vcar_arr_is_top` records that the arrow arm discards its value. If the
/// same collapse held at `ty` for a general `C`, every membership statement in
/// R18-R23 would be the top candidate in disguise and the normalization result
/// would say nothing at all. The kernel must refuse it.
#[test]
fn test_candmodel_r23_vcar_does_not_collapse_at_ty() {
    let mut spec = r23_spec();
    assert!(
        spec.add_recursive_def(&probe_vcar_ty_collapses(), "scope control")
            .is_err(),
        "vcarD collapses to the top candidate at ty as well as at an arrow — every membership \
         statement in R18-R23 is vacuous and the module doc is wrong"
    );
}

/// The adequacy induction reuses R12's candidate machinery and introduces no
/// new semantic machinery. Measured from the rung's OWN source.
#[test]
fn test_candmodel_r23_reuses_r12_candidate_machinery() {
    let src = val_xval_good();
    for required in [
        "WKC.rec",
        "goodSet_whnfAcc",
        "goodD_mkTyD",
        "isCandHI_piSet",
        "isCandHI_vcarD",
        "goodEnvD_vconsD",
        "goodD_junkD",
    ] {
        assert!(
            src.contains(required),
            "the adequacy induction no longer goes through {required}"
        );
    }
    for banned in ["sorry", "Classical", "axiom", "candInterp", "CandModel"] {
        assert!(
            !src.contains(banned),
            "the adequacy induction reaches {banned}, which no arm of it may"
        );
    }
}

/// The two new arms are the cheap ones the module doc claims, and are actually
/// present: `konst` really is `goodSet_whnfAcc`, and `let_` really extends the
/// valuation by the VALUE's interpretation.
#[test]
fn test_candmodel_r23_new_arms_are_what_the_doc_says() {
    let src = val_xval_good();
    assert!(
        src.contains("(qhrm : @Eq (OptionType RecMeta)") && src.contains("=> goodSet_whnfAcc)"),
        "the konst arm lost its inertness premises or is no longer goodSet_whnfAcc"
    );
    assert!(
        src.contains("qihgb (vconsD qsv qD (xval qD qv qsv qhv qr) qr)"),
        "the let_ arm no longer extends the valuation by the VALUE's interpretation"
    );
}

/// R22 named this rung's neighbourhood: the semantic stack was complete, and
/// what it did NOT do was a reducibility argument. This rung is that gap's
/// first instalment, so R22's disclaimer must still be there to be read.
#[test]
fn test_candmodel_r23_answers_the_gap_r22_disclaimed() {
    let doc = crate::test_utils::flatten_module_doc(include_str!("candmodel_construct_r22.rs"));
    assert!(
        doc.contains("It is not a reducibility argument"),
        "R22 no longer disclaims the reducibility argument — R23's premise has moved"
    );
}
