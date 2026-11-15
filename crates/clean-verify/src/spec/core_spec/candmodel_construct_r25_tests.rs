// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R25 tests — the arrow candidate, its two rules, and the refusals that pin
//! what each of them actually needs.

use super::super::candmodel_construct_r25_src::{
    probe_app_without_transport, probe_lam_without_acc, r25_all_sources, r25_items, val_red_app,
    val_red_lam,
};
use super::*;
use crate::test_utils::parse_check;

/// Register R25 into a freshly-built substitution spec if the bundle stage has
/// not already done it.
fn r25_spec() -> Specification {
    let mut spec = crate::test_utils::build_substitution_spec_with_stack();
    if spec.definitions().contains_key("r25_red_app") {
        return spec;
    }
    spec.add_candmodel_construct_r25()
        .expect("R25 should register into the substitution spec");
    spec
}

/// Parse every generated source.
#[test]
fn test_candmodel_r25_sources_parse() {
    for (name, src) in r25_all_sources() {
        parse_check(&src).unwrap_or_else(|e| panic!("R25 source {name} does not parse: {e}"));
    }
    parse_check(&probe_app_without_transport()).expect("the dropped-transport probe must parse");
    parse_check(&probe_lam_without_acc()).expect("the dropped-acc probe must parse");
}

/// No name registered twice, and the load-bearing ones are all present.
#[test]
fn test_candmodel_r25_names_are_unique() {
    let mut seen = std::collections::BTreeSet::new();
    for (name, _) in r25_all_sources() {
        assert!(seen.insert(name.clone()), "R25 registers {name} twice");
    }
    for required in [
        "r25_arrow",
        "r25_arrowWkc",
        "r25_red_arrow_is_the_function_space",
        "r25_red_app",
        "r25_red_lam",
        "r25_red_arrow_members_sn",
    ] {
        assert!(seen.contains(required), "R25 lost {required}");
    }
}

/// ITERATION TOOL — reports EVERY failure in one message.
#[test]
fn test_candmodel_r25_scratch_elaborates() {
    let mut spec = crate::test_utils::build_substitution_spec_with_stack();
    // WIRED-STATE BRANCH, deliberately NOT an early `return`. A bare return is a
    // self-skip: once the rung is in `bundles.rs` this test would report ok
    // forever, including if the stage were later dropped. Assert the rung's whole
    // table is live in the built spec instead, so the wired path carries a claim.
    if spec.definitions().contains_key("r25_red_app") {
        for (name, _) in r25_all_sources() {
            assert!(
                spec.env()
                    .get_const(&clean_kernel::Name::from_string(&name))
                    .is_some(),
                "R25 is wired but {name} is absent from the built spec"
            );
        }
    } else {
        let mut failures: Vec<String> = Vec::new();
        for item in r25_items() {
            match item {
                R25Item::Def { name, src } => {
                    if let Err(e) = spec.add_recursive_def(&src, "r25 scratch") {
                        failures.push(format!("DEF {name}: {e}"));
                    }
                }
                R25Item::Thm { name, ty, val } => {
                    if let Err(e) = add_thm(&mut spec, &name, ty, val, &[], "r25 scratch") {
                        failures.push(format!("THM {name}: {e}"));
                    }
                }
            }
        }
        assert!(
            failures.is_empty(),
            "R25 registration failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
    }
}

/// Every R25 constant is registered and every theorem re-verifies.
#[test]
fn test_candmodel_r25_registered_and_reverifies() {
    let spec = r25_spec();
    for (name, _) in r25_all_sources() {
        assert!(
            spec.definitions().contains_key(&name)
                || spec
                    .env()
                    .get_const(&clean_kernel::Name::from_string(&name))
                    .is_some(),
            "R25 constant {name} is not registered"
        );
    }
    for item in r25_items() {
        if let R25Item::Thm { name, .. } = item {
            spec.verify_definition(&name)
                .unwrap_or_else(|e| panic!("R25 theorem {name} does not re-verify: {e:?}"));
        }
    }
}

/// The type former and its derivation must stay reducible — every rule here
/// reduces through both.
#[test]
fn test_candmodel_r25_formers_delta_unfold() {
    use clean_kernel::{ConstantKind, Name};
    let spec = r25_spec();
    for op in ["r25_arrow", "r25_arrowWkc"] {
        let c = spec
            .env()
            .get_const(&Name::from_string(op))
            .unwrap_or_else(|| panic!("{op} missing from the R25 environment"));
        assert_eq!(
            c.kind,
            ConstantKind::Definition,
            "{op} must be a reducible Definition; Opaque stops the unfolding both rules depend on"
        );
    }
}

/// CENSUS. The computed axiom closure must be empty for every R25 constant.
#[test]
fn test_candmodel_r25_axiom_closure_is_empty() {
    let spec = r25_spec();
    for (name, _) in r25_all_sources() {
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

/// CENSUS, by kernel ground truth, over the bundle R25 actually changes.
#[test]
fn test_candmodel_r25_admits_no_new_census_axiom() {
    let spec = r25_spec();
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
        "R25 newly admitted kernel axioms into the substitution bundle: {newly:?}"
    );
}

/// MEASUREMENT: the lifted-codomain transport is load-bearing in the
/// elimination rule.
///
/// `xval`'s `pi` clause reads its codomain LIFTED at the junk extension, so
/// `hf a ha` inhabits that reading and not `B`'s own. Handing it back directly
/// must be refused. If it ever passes, the arrow candidate is reading its
/// codomain somewhere other than where this rung claims.
#[test]
fn test_candmodel_r25_app_needs_the_lift_transport() {
    let mut spec = r25_spec();
    assert!(
        spec.add_recursive_def(&probe_app_without_transport(), "transport control")
            .is_err(),
        "the elimination rule goes through without r20_xval_lift0 — the pi clause is not reading \
         its codomain lifted, and the type former's lift is unexplained"
    );
}

/// MEASUREMENT: the introduction rule needs the engine's `whnf_acc` premises.
#[test]
fn test_candmodel_r25_lam_needs_the_acc_premises() {
    let mut spec = r25_spec();
    assert!(
        spec.add_recursive_def(&probe_lam_without_acc(), "premise control")
            .is_err(),
        "the introduction rule goes through without whnf_acc of the annotation and body — R1's \
         engine premises are decoration"
    );
}

/// The two rules go through the pieces the module doc names, and nothing else.
#[test]
fn test_candmodel_r25_rules_use_the_named_machinery() {
    let app = val_red_app();
    let lam = val_red_lam();
    assert!(
        app.contains("r20_xval_lift0") && app.contains("Eq.substType"),
        "the elimination rule no longer goes through the lift transport"
    );
    assert!(
        lam.contains("r24_red_beta_expand") && lam.contains("r20_xval_lift0"),
        "the introduction rule no longer goes through R1's engine and the lift transport"
    );
    for banned in ["sorry", "Classical", "axiom", "candInterp", "KExpr.let_"] {
        assert!(
            !app.contains(banned) && !lam.contains(banned),
            "a rule reaches {banned}, which neither may — the fragment is zeta-free by design"
        );
    }
}

/// R24 named the gap this rung's rules are built for.
#[test]
fn test_candmodel_r25_follows_r24() {
    let doc = crate::test_utils::flatten_module_doc(include_str!("candmodel_construct_r24.rs"));
    assert!(
        doc.contains("term typing judgment on this lineage"),
        "R24 no longer names the term-judgment gap — R25's premise has moved"
    );
}
