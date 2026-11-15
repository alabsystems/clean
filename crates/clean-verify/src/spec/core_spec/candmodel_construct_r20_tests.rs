// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R20 tests — the native substitution lemma, the β law it buys, the bridge to
//! R18's transported statement, and the three refusals that bound all of it.

use super::super::candmodel_construct_r20_src::{
    probe_agrees_at_wkc, probe_beta_wrong_arg_shape, probe_psub_refl, r20_all_sources, r20_items,
    val_xval_psub,
};
use super::*;
use crate::test_utils::parse_check;

/// Register R20 into a freshly-built substitution spec if the bundle stage has
/// not already done it.
fn r20_spec() -> Specification {
    let mut spec = crate::test_utils::build_substitution_spec_with_stack();
    if spec.definitions().contains_key("r20_xval_psub") {
        return spec;
    }
    spec.add_candmodel_construct_r20()
        .expect("R20 should register into the substitution spec");
    spec
}

/// Parse every generated source. Microseconds, versus a whole spec build.
#[test]
fn test_candmodel_r20_sources_parse() {
    for (name, src) in r20_all_sources() {
        parse_check(&src).unwrap_or_else(|e| panic!("R20 source {name} does not parse: {e}"));
    }
    parse_check(&probe_psub_refl()).expect("the Eq.refl probe must parse");
    parse_check(&probe_agrees_at_wkc()).expect("the WKC-generalised agreement probe must parse");
    parse_check(&probe_beta_wrong_arg_shape()).expect("the beta shape probe must parse");
}

/// No name registered twice, and the load-bearing ones are all present.
#[test]
fn test_candmodel_r20_names_are_unique() {
    let mut seen = std::collections::BTreeSet::new();
    for (name, _) in r20_all_sources() {
        assert!(seen.insert(name.clone()), "R20 registers {name} twice");
    }
    for required in [
        "r20_xvenvSubD",
        "r20_xvenvSubD_agrees",
        "r20_xval_lift0",
        "r20_xval_cast_term",
        "r20_xvenvSub_up",
        "r20_xvenvSub_scons",
        "r20_xval_psub",
        "r20_xval_inst",
        "r20_xval_beta",
        "r20_psub_extends_transported",
        "r20_psub_reaches_konst",
        "r20_psub_reaches_let",
    ] {
        assert!(seen.contains(required), "R20 lost {required}");
    }
}

/// ITERATION TOOL. Registers the whole table and reports EVERY failure in one
/// message instead of dying on the first — the R13-R19 pattern.
#[test]
fn test_candmodel_r20_scratch_elaborates() {
    let mut spec = crate::test_utils::build_substitution_spec_with_stack();
    // WIRED-STATE BRANCH, deliberately NOT an early `return`. A bare return is a
    // self-skip: once the rung is in `bundles.rs` this test would report ok
    // forever, including if the stage were later dropped. Assert the rung's whole
    // table is live in the built spec instead, so the wired path carries a claim.
    if spec.definitions().contains_key("r20_xval_psub") {
        for (name, _) in r20_all_sources() {
            assert!(
                spec.env()
                    .get_const(&clean_kernel::Name::from_string(&name))
                    .is_some(),
                "R20 is wired but {name} is absent from the built spec"
            );
        }
    } else {
        let mut failures: Vec<String> = Vec::new();
        for item in r20_items() {
            match item {
                R20Item::Def { name, src } => {
                    if let Err(e) = spec.add_recursive_def(&src, "r20 scratch") {
                        failures.push(format!("DEF {name}: {e}"));
                    }
                }
                R20Item::Thm { name, ty, val } => {
                    if let Err(e) = add_thm(&mut spec, &name, ty, val, &[], "r20 scratch") {
                        failures.push(format!("THM {name}: {e}"));
                    }
                }
            }
        }
        assert!(
            failures.is_empty(),
            "R20 registration failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
    }
}

/// Every R20 constant is registered and every theorem re-verifies.
#[test]
fn test_candmodel_r20_registered_and_reverifies() {
    let spec = r20_spec();
    for (name, _) in r20_all_sources() {
        assert!(
            spec.definitions().contains_key(&name)
                || spec
                    .env()
                    .get_const(&clean_kernel::Name::from_string(&name))
                    .is_some(),
            "R20 constant {name} is not registered"
        );
    }
    for item in r20_items() {
        if let R20Item::Thm { name, .. } = item {
            spec.verify_definition(&name)
                .unwrap_or_else(|e| panic!("R20 theorem {name} does not re-verify: {e:?}"));
        }
    }
}

/// The two `add_recursive_def` constants must stay reducible. R12's measured
/// elaborator fact: an `add_definition` registration lowers to `Opaque` and
/// stops the reduction every later proof depends on — and `r20_xvenvSubD` is
/// read through by every arm of the substitution lemma.
#[test]
fn test_candmodel_r20_reduction_spine_delta_unfolds() {
    use clean_kernel::{ConstantKind, Name};
    let spec = r20_spec();
    for op in ["r20_xvenvSubD", "r20_idsubst_typed"] {
        let c = spec
            .env()
            .get_const(&Name::from_string(op))
            .unwrap_or_else(|| panic!("{op} missing from the R20 environment"));
        assert_eq!(
            c.kind,
            ConstantKind::Definition,
            "{op} must be a reducible Definition; Opaque or Theorem stops the reduction the \
             substitution lemma's var arm depends on"
        );
    }
}

/// CENSUS. The computed axiom closure — by kernel ground truth — must be empty
/// for every R20 constant.
#[test]
fn test_candmodel_r20_axiom_closure_is_empty() {
    let spec = r20_spec();
    for (name, _) in r20_all_sources() {
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

/// CENSUS, by kernel ground truth, over the bundle R20 actually changes.
#[test]
fn test_candmodel_r20_admits_no_new_census_axiom() {
    let spec = r20_spec();
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
        "R20 newly admitted kernel axioms into the substitution bundle: {newly:?}"
    );
}

/// MEASUREMENT: the native substitution lemma is NOT a definitional identity.
#[test]
fn test_candmodel_r20_psub_is_not_definitional() {
    let mut spec = r20_spec();
    assert!(
        spec.add_recursive_def(&probe_psub_refl(), "negative control")
            .is_err(),
        "the native substitution lemma is DEFINITIONAL — the seven-arm induction witnesses nothing"
    );
}

/// THE SCOPE OF THE BRIDGE, made machine-visible.
///
/// `r20_xvenvSubD_agrees` relates the new valuation construction to `venvSubD`
/// only at an EMBEDDED substitution hypothesis. This probe claims it at an
/// arbitrary `WKC` one with the same proof; the kernel must refuse, because
/// `venvSubD` takes a `WK`-typed hypothesis and at a `konst`- or `let_`-headed
/// substitution there is none to hand. If this ever passes, the new
/// construction is not actually wider than the old one and the rung's premise
/// is wrong.
#[test]
fn test_candmodel_r20_bridge_is_narrower_than_the_definition() {
    let mut spec = r20_spec();
    assert!(
        spec.add_recursive_def(&probe_agrees_at_wkc(), "scope control")
            .is_err(),
        "r20_xvenvSubD_agrees went through at an arbitrary WKC substitution — venvSubD is not \
         WK-indexed after all, and R18's recorded caveat was never real"
    );
}

/// MEASUREMENT: the β law reads `WKC.app`'s real shape discipline.
///
/// `WKC.app`'s function premise is at `Sk.arr (domSk d) c`, so the argument must
/// inhabit `domSk d`. This probe types it at `d` instead; the kernel must
/// refuse. If it were accepted, `domSk` would be collapsing and
/// `r20_xval_beta` would be succeeding for a reason that has nothing to do with
/// β.
#[test]
fn test_candmodel_r20_beta_respects_the_domain_shape() {
    let mut spec = r20_spec();
    assert!(
        spec.add_recursive_def(&probe_beta_wrong_arg_shape(), "shape control")
            .is_err(),
        "the beta law typechecks with its argument at d rather than domSk d — domSk is collapsing \
         and the law measures nothing about WKC.app"
    );
}

/// The native induction reuses R13's and R14's helpers and introduces no new
/// semantic machinery. Measured from the rung's OWN source.
#[test]
fn test_candmodel_r20_reuses_r13_r14_helpers_verbatim() {
    let src = val_xval_psub();
    for required in [
        "WKC.rec",
        "r14_sval_pi_congr",
        "r14_vapply_congr",
        "r13_vd_arr_funext",
        "r20_xvenvSub_up",
        "r20_xvenvSubD",
    ] {
        assert!(
            src.contains(required),
            "the native substitution induction no longer goes through {required}"
        );
    }
    for banned in ["sorry", "Classical", "axiom", "candInterp"] {
        assert!(
            !src.contains(banned),
            "the native substitution induction reaches {banned}, which no arm of it may"
        );
    }
}

/// R19 named this rung's subject. If that sentence leaves R19, the ladder's
/// reading order is broken.
#[test]
fn test_candmodel_r20_closes_the_item_r19_named() {
    let doc = crate::test_utils::flatten_module_doc(include_str!("candmodel_construct_r19.rs"));
    assert!(
        doc.contains("a native `psub` needs a `WKC`-indexed valuation"),
        "R19 no longer names val_psub, or the reason it needed a definition first — R20's premise has moved"
    );
}
