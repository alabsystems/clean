// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R28 tests — the type class, the generalisation that makes its lift lemma
//! provable, and the two refusals that measure both.

use super::super::candmodel_construct_r28_src::{
    probe_lift_fixed_depth, r28_all_sources, r28_items, val_inert_lift, val_inert_whnf_acc,
};
use super::*;
use crate::test_utils::parse_check;

/// Register R28 into a freshly-built substitution spec if the bundle stage has
/// not already done it.
fn r28_spec() -> Specification {
    let mut spec = crate::test_utils::build_substitution_spec_with_stack();
    if spec.definitions().contains_key("r28_inertTy_wkc") {
        return spec;
    }
    spec.add_candmodel_construct_r28()
        .expect("R28 should register into the substitution spec");
    spec
}

/// Parse every generated source. Microseconds, versus a whole spec build.
#[test]
fn test_candmodel_r28_sources_parse() {
    for (name, src) in r28_all_sources() {
        parse_check(&src).unwrap_or_else(|e| panic!("R28 source {name} does not parse: {e}"));
    }
    parse_check(&probe_lift_fixed_depth()).expect("the fixed-depth probe must parse");
}

/// No name registered twice, and the load-bearing ones are all present.
#[test]
fn test_candmodel_r28_names_are_unique() {
    let mut seen = std::collections::BTreeSet::new();
    for (name, _) in r28_all_sources() {
        assert!(seen.insert(name.clone()), "R28 registers {name} twice");
    }
    for required in [
        "InertTy",
        "r28_inertTy_wkc",
        "r28_inertTy_lift",
        "r28_inertTy_psubst",
        "r28_inertTy_whnfAcc",
        "r28_notBvar",
        "r28_inertTy_not_total",
    ] {
        assert!(seen.contains(required), "R28 lost {required}");
    }
}

/// ITERATION TOOL. Registers the whole table and reports EVERY failure in one
/// message instead of dying on the first — the R13-R27 pattern.
#[test]
fn test_candmodel_r28_scratch_elaborates() {
    let mut spec = crate::test_utils::build_substitution_spec_with_stack();
    // WIRED-STATE BRANCH, deliberately NOT an early `return`. A bare return is a
    // self-skip: once the rung is in `bundles.rs` this test would report ok
    // forever, including if the stage were later dropped. Assert the rung's whole
    // table is live in the built spec instead, so the wired path carries a claim.
    if spec.definitions().contains_key("r28_inertTy_wkc") {
        for (name, _) in r28_all_sources() {
            assert!(
                spec.env()
                    .get_const(&clean_kernel::Name::from_string(&name))
                    .is_some(),
                "R28 is wired but {name} is absent from the built spec"
            );
        }
    } else {
        let mut failures: Vec<String> = Vec::new();
        for item in r28_items() {
            match item {
                R28Item::Ind { name, src } => {
                    if let Err(e) = spec.add_inductive(&src, "r28 scratch") {
                        failures.push(format!("IND {name}: {e}"));
                    }
                }
                R28Item::Def { name, src } => {
                    if let Err(e) = spec.add_recursive_def(&src, "r28 scratch") {
                        failures.push(format!("DEF {name}: {e}"));
                    }
                }
                R28Item::Thm { name, ty, val } => {
                    if let Err(e) = add_thm(&mut spec, &name, ty, val, &[], "r28 scratch") {
                        failures.push(format!("THM {name}: {e}"));
                    }
                }
            }
        }
        assert!(
            failures.is_empty(),
            "R28 registration failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
    }
}

/// Every R28 constant is registered and every theorem re-verifies.
#[test]
fn test_candmodel_r28_registered_and_reverifies() {
    let spec = r28_spec();
    for (name, _) in r28_all_sources() {
        assert!(
            spec.definitions().contains_key(&name)
                || spec
                    .env()
                    .get_const(&clean_kernel::Name::from_string(&name))
                    .is_some(),
            "R28 constant {name} is not registered"
        );
    }
    for item in r28_items() {
        if let R28Item::Thm { name, .. } = item {
            spec.verify_definition(&name)
                .unwrap_or_else(|e| panic!("R28 theorem {name} does not re-verify: {e:?}"));
        }
    }
}

/// CENSUS. The computed axiom closure — by kernel ground truth — must be empty
/// for every R28 constant.
#[test]
fn test_candmodel_r28_axiom_closure_is_empty() {
    let spec = r28_spec();
    for (name, _) in r28_all_sources() {
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

/// CENSUS, by kernel ground truth, over the bundle R28 actually changes.
#[test]
fn test_candmodel_r28_admits_no_new_census_axiom() {
    let spec = r28_spec();
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
        "R28 newly admitted kernel axioms into the substitution bundle: {newly:?}"
    );
}

/// NON-DEGENERACY is a REGISTERED THEOREM here, not a refused probe — so this
/// test checks it is registered and reachable, not that something is refused.
///
/// The distinction is the reason `r28_inertTy_not_total` exists: a refusal says
/// the kernel would not accept one particular derivation, while the theorem
/// says no derivation exists at all. If `InertTy` were degenerate, all four
/// lemmas above would be kernel-checked statements about everything.
#[test]
fn test_candmodel_r28_non_degeneracy_is_a_theorem() {
    let spec = r28_spec();
    let def = spec
        .definitions()
        .get("r28_inertTy_not_total")
        .expect("the non-degeneracy theorem must be registered");
    assert!(
        !def.is_axiom && def.value_src.is_some(),
        "non-degeneracy carries no proof term — a value-less definition lowers to a kernel \
         axiom, which for this statement would be ASSUMING the class is not degenerate"
    );
    assert!(
        def.type_src
            .contains("InertTy (KExpr.bvar Nat.zero) -> Empty"),
        "the non-degeneracy statement drifted: {}",
        def.type_src
    );
    spec.verify_definition("r28_inertTy_not_total")
        .expect("non-degeneracy must re-verify");
}

/// MEASUREMENT: the lift lemma's `d`/`k` quantification is LOAD-BEARING.
///
/// This is the rung's central claim, and it is claimed by refusal rather than
/// argued. `r28_inertTy_lift` is generalised over cutoff and amount because the
/// single instance the fundamental theorem wants — `lift_at T 0 1 = T` — does
/// not admit an induction: `lift_at`'s `pi` clause recurses on the codomain at
/// `Nat.succ cutoff`, so the arrow arm needs the lemma at depth 1 while the
/// fixed statement only ever supplies depth 0. The probe states exactly that
/// fixed instance and closes the arrow arm with `Eq.refl`; the kernel must
/// refuse. If it ever passes, the generalisation is decoration and this rung's
/// argument — and the paragraph in the design doc that calls the closedness
/// bridge unnecessary — is wrong.
#[test]
fn test_candmodel_r28_lift_generalisation_is_load_bearing() {
    let mut spec = r28_spec();
    assert!(
        spec.add_recursive_def(&probe_lift_fixed_depth(), "generalisation control")
            .is_err(),
        "the FIXED-depth lift lemma went through by Eq.refl — lift_at does not recurse at \
         Nat.succ cutoff after all, and the d/k generalisation is buying nothing"
    );
}

/// The two lemmas that see through `r25_arrow`'s lift really do go through
/// `r28_inertTy_lift`, and neither smuggles in an axiom-shaped escape hatch.
/// Measured from the rung's OWN source.
#[test]
fn test_candmodel_r28_pays_for_the_lift_exactly_once() {
    for (what, src) in [
        ("whnfAcc", val_inert_whnf_acc()),
        ("lift", val_inert_lift()),
    ] {
        for banned in ["sorry", "Classical", "axiom", "is_closed_at", "candInterp"] {
            assert!(
                !src.contains(banned),
                "the {what} induction reaches {banned}, which no arm of it may — and \
                 is_closed_at in particular would mean the closedness bridge came back"
            );
        }
    }
    assert!(
        val_inert_whnf_acc().contains("r28_inertTy_lift")
            && val_inert_whnf_acc().contains("whnfAcc_pi")
            && val_inert_whnf_acc().contains("r17_const_no_step"),
        "the SN lemma no longer goes through the lift lemma, whnfAcc_pi and the const inverter"
    );
    assert!(
        val_inert_lift().contains("ihB Nat.zero (Nat.succ Nat.zero)"),
        "the lift lemma's arrow arm no longer uses its IH at (0, 1) to see through r25_arrow's \
         own lift — which is the step the generalisation exists for"
    );
}

/// R27 named this rung's subject. If that sentence leaves R27, the ladder's
/// reading order is broken.
#[test]
fn test_candmodel_r28_closes_the_item_r27_named() {
    let doc = crate::test_utils::flatten_module_doc(include_str!("candmodel_construct_r27.rs"));
    assert!(
        doc.contains("the JUDGMENT, not a lemma"),
        "R27 no longer names the term judgment as its successor — R28's premise has moved"
    );
}
