// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R19 tests — the native induction, the two arms no embedding reaches, the
//! drift check against R18, and the refusals that measure both.

use super::super::candmodel_construct_r19_src::{
    probe_konst_arm_wrong_shape, probe_native_refl, r19_all_sources, r19_items,
    val_xval_lift_native,
};
use super::*;
use crate::test_utils::parse_check;

/// Register R19 into a freshly-built substitution spec if the bundle stage has
/// not already done it.
fn r19_spec() -> Specification {
    let mut spec = crate::test_utils::build_substitution_spec_with_stack();
    if spec.definitions().contains_key("r19_xval_lift") {
        return spec;
    }
    spec.add_candmodel_construct_r19()
        .expect("R19 should register into the substitution spec");
    spec
}

/// Parse every generated source. Microseconds, versus a whole spec build.
#[test]
fn test_candmodel_r19_sources_parse() {
    for (name, src) in r19_all_sources() {
        parse_check(&src).unwrap_or_else(|e| panic!("R19 source {name} does not parse: {e}"));
    }
    parse_check(&probe_native_refl()).expect("the Eq.refl probe must parse");
    parse_check(&probe_konst_arm_wrong_shape()).expect("the konst shape probe must parse");
}

/// No name registered twice, and the load-bearing ones are all present.
#[test]
fn test_candmodel_r19_names_are_unique() {
    let mut seen = std::collections::BTreeSet::new();
    for (name, _) in r19_all_sources() {
        assert!(seen.insert(name.clone()), "R19 registers {name} twice");
    }
    for required in [
        "r19_xval_wkc_lift_var",
        "r19_xval_lift",
        "r19_native_extends_transported",
        "r19_lift_reaches_konst",
        "r19_lift_reaches_let",
    ] {
        assert!(seen.contains(required), "R19 lost {required}");
    }
}

/// ITERATION TOOL. Registers the whole table and reports EVERY failure in one
/// message instead of dying on the first — the R13-R18 pattern.
#[test]
fn test_candmodel_r19_scratch_elaborates() {
    let mut spec = crate::test_utils::build_substitution_spec_with_stack();
    // WIRED-STATE BRANCH, deliberately NOT an early `return`. A bare return is a
    // self-skip: once the rung is in `bundles.rs` this test would report ok
    // forever, including if the stage were later dropped. Assert the rung's whole
    // table is live in the built spec instead, so the wired path carries a claim.
    if spec.definitions().contains_key("r19_xval_lift") {
        for (name, _) in r19_all_sources() {
            assert!(
                spec.env()
                    .get_const(&clean_kernel::Name::from_string(&name))
                    .is_some(),
                "R19 is wired but {name} is absent from the built spec"
            );
        }
    } else {
        let mut failures: Vec<String> = Vec::new();
        for item in r19_items() {
            let R19Item::Thm { name, ty, val } = item;
            if let Err(e) = add_thm(&mut spec, &name, ty, val, &[], "r19 scratch") {
                failures.push(format!("THM {name}: {e}"));
            }
        }
        assert!(
            failures.is_empty(),
            "R19 registration failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
    }
}

/// Every R19 constant is registered and every theorem re-verifies.
#[test]
fn test_candmodel_r19_registered_and_reverifies() {
    let spec = r19_spec();
    for (name, _) in r19_all_sources() {
        assert!(
            spec.definitions().contains_key(&name)
                || spec
                    .env()
                    .get_const(&clean_kernel::Name::from_string(&name))
                    .is_some(),
            "R19 constant {name} is not registered"
        );
        spec.verify_definition(&name)
            .unwrap_or_else(|e| panic!("R19 theorem {name} does not re-verify: {e:?}"));
    }
}

/// CENSUS. The computed axiom closure — by kernel ground truth — must be empty
/// for every R19 constant.
#[test]
fn test_candmodel_r19_axiom_closure_is_empty() {
    let spec = r19_spec();
    for (name, _) in r19_all_sources() {
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

/// CENSUS, by kernel ground truth, over the bundle R19 actually changes.
#[test]
fn test_candmodel_r19_admits_no_new_census_axiom() {
    let spec = r19_spec();
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
        "R19 newly admitted kernel axioms into the substitution bundle: {newly:?}"
    );
}

/// MEASUREMENT: the native lemma is NOT a definitional identity. Both sides are
/// `WKC.rec` stuck on a variable derivation, so `Eq.refl` cannot prove it and
/// the kernel must refuse — without this the induction could be vacuous work.
#[test]
fn test_candmodel_r19_native_lift_is_not_definitional() {
    let mut spec = r19_spec();
    assert!(
        spec.add_recursive_def(&probe_native_refl(), "negative control")
            .is_err(),
        "the native weakening lemma is DEFINITIONAL — the seven-arm induction witnesses nothing"
    );
}

/// MEASUREMENT: the `konst` arm's `Eq.refl` is reading the real clause.
///
/// `WKC.konst` concludes at `Sk.ty` and at no other shape — R17's
/// `r17_headFree_wkc_arr`, and with it the whole subject-reduction route, rests
/// on exactly that. The same reflexivity claimed at an ARROW shape must be
/// refused; if it were accepted, `VD` would be collapsing shapes and the arm's
/// `Eq.refl` would be succeeding by accident rather than because the clause
/// discards its valuation.
#[test]
fn test_candmodel_r19_konst_arm_is_shape_specific() {
    let mut spec = r19_spec();
    assert!(
        spec.add_recursive_def(&probe_konst_arm_wrong_shape(), "shape control")
            .is_err(),
        "the konst arm's Eq.refl typechecks at an ARROW shape too — VD is collapsing shapes and \
         the arm proves nothing about xval's konst clause"
    );
}

/// The native proof reuses R13's and R14's helpers and introduces no new
/// semantic machinery of its own. Measured from the rung's OWN source, so a
/// later edit that smuggles in a fresh lemma — or an axiom-shaped escape hatch
/// — fails here rather than quietly widening the trust story.
#[test]
fn test_candmodel_r19_reuses_r13_r14_helpers_verbatim() {
    let src = val_xval_lift_native();
    for required in [
        "WKC.rec",
        "r14_sval_pi_congr",
        "r14_vapply_congr",
        "r13_vd_arr_funext",
        "r14_venvLift_vcons",
        "r19_xval_wkc_lift_var",
    ] {
        assert!(
            src.contains(required),
            "the native induction no longer goes through {required}"
        );
    }
    for banned in ["sorry", "Classical", "axiom", "candInterp"] {
        assert!(
            !src.contains(banned),
            "the native induction reaches {banned}, which no arm of it may"
        );
    }
}

/// The two arms that are the rung's whole point are actually present in the
/// induction, and the `konst` one really is the trivial denotation.
#[test]
fn test_candmodel_r19_has_the_two_new_arms() {
    let src = val_xval_lift_native();
    assert!(
        src.contains("qhd : @Eq (OptionType KExpr) (defval_for"),
        "the konst arm lost its inertness premises — it is no longer WKC.konst's minor"
    );
    assert!(
        src.contains("(qtt : KExpr)") && src.contains("qihb (Nat.succ qk) qins (vconsD qsv"),
        "the let_ arm no longer feeds the body hypothesis the VALUE-extended valuation"
    );
}

/// R18 named this rung's subject. If that sentence leaves R18, the ladder's
/// reading order is broken.
#[test]
fn test_candmodel_r19_closes_the_item_r18_named() {
    let doc = crate::test_utils::flatten_module_doc(include_str!("candmodel_construct_r18.rs"));
    assert!(
        doc.contains("NATIVE semantics at `konst` and `let_`"),
        "R18 no longer names xval-native semantics as its next item — R19's premise has moved"
    );
}
