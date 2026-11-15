// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R29 tests — the judgment, the fundamental theorem, the capstone, and the
//! refusal that keeps the reducible-substitution premise load-bearing.

use super::super::candmodel_construct_r29_src::{
    probe_no_redsub, r29_all_sources, r29_items, val_fundamental,
};
use super::*;
use crate::test_utils::parse_check;

/// Register R29 — and R28 first when the bundle stages are not yet wired,
/// because every R29 statement is over `InertTy` and its four facts.
fn r29_spec() -> Specification {
    let mut spec = crate::test_utils::build_substitution_spec_with_stack();
    if spec.definitions().contains_key("r29_fundamental") {
        return spec;
    }
    if !spec.definitions().contains_key("r28_inertTy_wkc") {
        spec.add_candmodel_construct_r28()
            .expect("R28 is R29's vocabulary and must register first");
    }
    spec.add_candmodel_construct_r29()
        .expect("R29 should register into the substitution spec");
    spec
}

/// Parse every generated source. Microseconds, versus a whole spec build.
#[test]
fn test_candmodel_r29_sources_parse() {
    for (name, src) in r29_all_sources() {
        parse_check(&src).unwrap_or_else(|e| panic!("R29 source {name} does not parse: {e}"));
    }
    parse_check(&probe_no_redsub()).expect("the missing-hypothesis probe must parse");
}

/// No name registered twice, and the load-bearing ones are all present.
#[test]
fn test_candmodel_r29_names_are_unique() {
    let mut seen = std::collections::BTreeSet::new();
    for (name, _) in r29_all_sources() {
        assert!(seen.insert(name.clone()), "R29 registers {name} twice");
    }
    for required in [
        "r29_tcons",
        "r29_ctxOK",
        "r29_ctxOK_cons",
        "TmC",
        "r29_RedSub",
        "r29_redsub_id",
        "r29_redsub_extend",
        "r29_fundamental",
        "r29_sn",
    ] {
        assert!(seen.contains(required), "R29 lost {required}");
    }
}

/// ITERATION TOOL. Registers the whole table and reports EVERY failure in one
/// message instead of dying on the first — the R13-R28 pattern.
#[test]
fn test_candmodel_r29_scratch_elaborates() {
    let mut spec = crate::test_utils::build_substitution_spec_with_stack();
    // WIRED-STATE BRANCH, deliberately NOT an early `return`. A bare return is a
    // self-skip: once the rung is in `bundles.rs` this test would report ok
    // forever, including if the stage were later dropped. Assert the rung's whole
    // table is live in the built spec instead, so the wired path carries a claim.
    if spec.definitions().contains_key("r29_fundamental") {
        for (name, _) in r29_all_sources() {
            assert!(
                spec.env()
                    .get_const(&clean_kernel::Name::from_string(&name))
                    .is_some(),
                "R29 is wired but {name} is absent from the built spec"
            );
        }
    } else {
        if !spec.definitions().contains_key("r28_inertTy_wkc") {
            spec.add_candmodel_construct_r28()
                .expect("R28 is R29's vocabulary and must register first");
        }
        let mut failures: Vec<String> = Vec::new();
        for item in r29_items() {
            match item {
                R29Item::Ind { name, src } => {
                    if let Err(e) = spec.add_inductive(&src, "r29 scratch") {
                        failures.push(format!("IND {name}: {e}"));
                    }
                }
                R29Item::Def { name, src } => {
                    if let Err(e) = spec.add_recursive_def(&src, "r29 scratch") {
                        failures.push(format!("DEF {name}: {e}"));
                    }
                }
                R29Item::Thm { name, ty, val } => {
                    if let Err(e) = add_thm(&mut spec, &name, ty, val, &[], "r29 scratch") {
                        failures.push(format!("THM {name}: {e}"));
                    }
                }
            }
        }
        assert!(
            failures.is_empty(),
            "R29 registration failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
    }
}

/// Every R29 constant is registered and every theorem re-verifies.
#[test]
fn test_candmodel_r29_registered_and_reverifies() {
    let spec = r29_spec();
    for (name, _) in r29_all_sources() {
        assert!(
            spec.definitions().contains_key(&name)
                || spec
                    .env()
                    .get_const(&clean_kernel::Name::from_string(&name))
                    .is_some(),
            "R29 constant {name} is not registered"
        );
    }
    for item in r29_items() {
        if let R29Item::Thm { name, .. } = item {
            spec.verify_definition(&name)
                .unwrap_or_else(|e| panic!("R29 theorem {name} does not re-verify: {e:?}"));
        }
    }
}

/// CENSUS. The computed axiom closure — by kernel ground truth — must be empty
/// for every R29 constant.
#[test]
fn test_candmodel_r29_axiom_closure_is_empty() {
    let spec = r29_spec();
    for (name, _) in r29_all_sources() {
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

/// CENSUS, by kernel ground truth, over the bundle R29 actually changes.
#[test]
fn test_candmodel_r29_admits_no_new_census_axiom() {
    let spec = r29_spec();
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
        "R29 newly admitted kernel axioms into the substitution bundle: {newly:?}"
    );
}

/// THE REDUCIBLE-SUBSTITUTION PREMISE IS LOAD-BEARING.
///
/// A fundamental theorem whose substitution hypothesis did nothing would be a
/// statement about every substitution, which is false the moment a variable
/// appears — the `var` arm returns exactly that hypothesis at `i`, and has
/// nothing else to return. The probe claims the conclusion with the premise
/// deleted and proves it with the same term; the kernel must refuse.
#[test]
fn test_candmodel_r29_reducible_substitution_is_load_bearing() {
    let mut spec = r29_spec();
    assert!(
        spec.add_recursive_def(&probe_no_redsub(), "premise control")
            .is_err(),
        "the fundamental theorem went through with NO hypothesis on the substitution — the var \
         arm is not reading it and the theorem measures nothing"
    );
}

/// The `lam` arm really does close the way this rung says it does.
///
/// Three names are the whole argument and none is optional: `r27_red_var` at
/// `bvar 0`, which makes the family instance available at a term that is
/// reducible at ANY type; `whnfAcc_of_instantiate_bvar0`, which strips the
/// instantiation off the SN it yields; and `r26_lam_premise_is_the_induction_hypothesis`,
/// which is what turns the induction hypothesis at `scons a2 s` into the
/// contractum `r26_red_lam_one` asks for. If any leaves the term, the arm is
/// closing some other way and the module doc is wrong.
#[test]
fn test_candmodel_r29_lam_arm_reads_sn_off_its_own_family_instance() {
    let src = val_fundamental();
    for required in [
        "whnfAcc_of_instantiate_bvar0",
        "r27_red_var D A (r28_inertTy_wkc D A hA) r hr Nat.zero",
        "r26_lam_premise_is_the_induction_hypothesis",
        "r29_redsub_extend",
        "isCandHF_cr1",
        "r26_red_lam_one",
        "r25_red_app",
        "r27_red_irrel",
    ] {
        assert!(
            src.contains(required),
            "the fundamental theorem no longer goes through {required}"
        );
    }
    for banned in ["sorry", "Classical", "axiom", "candInterp", "betaStar"] {
        assert!(
            !src.contains(banned),
            "the fundamental theorem reaches {banned} — and `betaStar` in particular would mean \
             R6's development family came back, which this rung's whole argument is that it \
             need not"
        );
    }
}

/// R28 named this rung's subject. If that sentence leaves R28, the ladder's
/// reading order is broken.
#[test]
fn test_candmodel_r29_closes_the_item_r28_named() {
    let doc = crate::test_utils::flatten_module_doc(include_str!("candmodel_construct_r28.rs"));
    assert!(
        doc.contains("It is not the judgment."),
        "R28 no longer names the judgment as its successor — R29's premise has moved"
    );
}
