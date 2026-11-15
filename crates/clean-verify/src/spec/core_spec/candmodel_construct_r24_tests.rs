// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R24 tests — the reducibility interface, the β engine on it, and the two
//! refusals that bound it.

use super::super::candmodel_construct_r24_src::{
    probe_candhf_without_env, probe_zeta_engine_at_red, r24_all_sources, r24_items,
    ty_beta_holds_zeta_refuted, zeta_engine_hypothesis_for_test,
};
use super::*;
use crate::test_utils::parse_check;

/// Register R24 into a freshly-built substitution spec if the bundle stage has
/// not already done it.
fn r24_spec() -> Specification {
    let mut spec = crate::test_utils::build_substitution_spec_with_stack();
    if spec.definitions().contains_key("r24_red_beta_expand") {
        return spec;
    }
    spec.add_candmodel_construct_r24()
        .expect("R24 should register into the substitution spec");
    spec
}

/// Parse every generated source.
#[test]
fn test_candmodel_r24_sources_parse() {
    for (name, src) in r24_all_sources() {
        parse_check(&src).unwrap_or_else(|e| panic!("R24 source {name} does not parse: {e}"));
    }
    parse_check(&probe_zeta_engine_at_red()).expect("the zeta engine probe must parse");
    parse_check(&probe_candhf_without_env()).expect("the dropped-env probe must parse");
}

/// No name registered twice, and the load-bearing ones are all present.
#[test]
fn test_candmodel_r24_names_are_unique() {
    let mut seen = std::collections::BTreeSet::new();
    for (name, _) in r24_all_sources() {
        assert!(seen.insert(name.clone()), "R24 registers {name} twice");
    }
    for required in [
        "r24_RedAt",
        "r24_red_isCandHF",
        "r24_red_beta_expand",
        "r24_red_members_sn",
        "r24_red_excludes_omega",
        "r24_red_conv_stable",
    ] {
        assert!(seen.contains(required), "R24 lost {required}");
    }
}

/// ITERATION TOOL — reports EVERY failure in one message.
#[test]
fn test_candmodel_r24_scratch_elaborates() {
    let mut spec = crate::test_utils::build_substitution_spec_with_stack();
    // WIRED-STATE BRANCH, deliberately NOT an early `return`. A bare return is a
    // self-skip: once the rung is in `bundles.rs` this test would report ok
    // forever, including if the stage were later dropped. Assert the rung's whole
    // table is live in the built spec instead, so the wired path carries a claim.
    if spec.definitions().contains_key("r24_red_beta_expand") {
        for (name, _) in r24_all_sources() {
            assert!(
                spec.env()
                    .get_const(&clean_kernel::Name::from_string(&name))
                    .is_some(),
                "R24 is wired but {name} is absent from the built spec"
            );
        }
    } else {
        let mut failures: Vec<String> = Vec::new();
        for item in r24_items() {
            match item {
                R24Item::Def { name, src } => {
                    if let Err(e) = spec.add_recursive_def(&src, "r24 scratch") {
                        failures.push(format!("DEF {name}: {e}"));
                    }
                }
                R24Item::Thm { name, ty, val } => {
                    if let Err(e) = add_thm(&mut spec, &name, ty, val, &[], "r24 scratch") {
                        failures.push(format!("THM {name}: {e}"));
                    }
                }
            }
        }
        assert!(
            failures.is_empty(),
            "R24 registration failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
    }
}

/// Every R24 constant is registered and every theorem re-verifies.
#[test]
fn test_candmodel_r24_registered_and_reverifies() {
    let spec = r24_spec();
    for (name, _) in r24_all_sources() {
        assert!(
            spec.definitions().contains_key(&name)
                || spec
                    .env()
                    .get_const(&clean_kernel::Name::from_string(&name))
                    .is_some(),
            "R24 constant {name} is not registered"
        );
    }
    for item in r24_items() {
        if let R24Item::Thm { name, .. } = item {
            spec.verify_definition(&name)
                .unwrap_or_else(|e| panic!("R24 theorem {name} does not re-verify: {e:?}"));
        }
    }
}

/// `r24_RedAt` must stay reducible — every theorem here reduces through it.
#[test]
fn test_candmodel_r24_redat_delta_unfolds() {
    use clean_kernel::{ConstantKind, Name};
    let spec = r24_spec();
    let c = spec
        .env()
        .get_const(&Name::from_string("r24_RedAt"))
        .expect("r24_RedAt missing from the R24 environment");
    assert_eq!(
        c.kind,
        ConstantKind::Definition,
        "r24_RedAt must be a reducible Definition; Opaque stops every proof in this rung"
    );
}

/// CENSUS. The computed axiom closure must be empty for every R24 constant.
#[test]
fn test_candmodel_r24_axiom_closure_is_empty() {
    let spec = r24_spec();
    for (name, _) in r24_all_sources() {
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

/// CENSUS, by kernel ground truth, over the bundle R24 actually changes.
#[test]
fn test_candmodel_r24_admits_no_new_census_axiom() {
    let spec = r24_spec();
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
        "R24 newly admitted kernel axioms into the substitution bundle: {newly:?}"
    );
}

/// THE ζ HALF, MACHINE-VISIBLE.
///
/// The same engine stated at `r24_RedAt` with the redex swapped to
/// `let_ ty a b`, proved the way the β one is. The kernel must refuse it:
/// `candExpHF_beta`'s conclusion is the application redex, and R1 proved there
/// is no per-set engine yielding the `let_` one. If this ever passes, either
/// `Neutral` has changed at `let_` or R1's refutation has been contradicted,
/// and both are load-bearing for the ladder.
#[test]
fn test_candmodel_r24_zeta_engine_is_refused() {
    let mut spec = r24_spec();
    assert!(
        spec.add_recursive_def(&probe_zeta_engine_at_red(), "zeta control")
            .is_err(),
        "the zeta engine went through at r24_RedAt — R1's zeta_expansion_not_generic is \
         contradicted, or Neutral at let_ has changed"
    );
}

/// MEASUREMENT: candidacy needs a GOOD valuation.
#[test]
fn test_candmodel_r24_candidacy_needs_a_good_valuation() {
    let mut spec = r24_spec();
    assert!(
        spec.add_recursive_def(&probe_candhf_without_env(), "premise control")
            .is_err(),
        "r24_RedAt is a candidate without GoodEnvD — R23's adequacy premise is decoration"
    );
}

/// THE CONTRAST, carried mechanically.
///
/// The intended single `AndType` constant does not typecheck — `GoodEnvD` is a
/// `Type 1` and `AndType` is `Type 0`-valued in this non-cumulative kernel, so
/// the kernel reports `universe level conflict: 1 vs 0`. The contrast is
/// therefore three facts: the β engine is REGISTERED, R1's ζ refutation is
/// REGISTERED, and the ζ engine at `r24_RedAt` is REFUSED (the test above).
/// This one pins the remaining half — that the two engine SHAPES still differ
/// in exactly the redex and nothing else, which is what makes the refutation
/// bear on the engine at all.
#[test]
fn test_candmodel_r24_beta_and_zeta_engines_differ_only_in_the_redex() {
    let spec = r24_spec();
    for required in ["r24_red_beta_expand", "zeta_expansion_not_generic"] {
        assert!(
            spec.definitions().contains_key(required)
                || spec
                    .env()
                    .get_const(&clean_kernel::Name::from_string(required))
                    .is_some(),
            "{required} is not registered — the contrast has lost a half"
        );
    }
    let beta = ty_beta_holds_zeta_refuted();
    assert!(
        beta.contains("(KExpr.app (KExpr.lam qlamTy qb) qa)"),
        "the beta engine no longer concludes at the BETA redex"
    );
    let zeta = zeta_engine_hypothesis_for_test();
    assert!(
        zeta.contains("S (KExpr.let_ ty a b)"),
        "R1's refuted engine no longer concludes at the ZETA redex"
    );
    for shared in ["whnf_acc", "betaStar", "instantiate"] {
        assert!(
            zeta.contains(shared),
            "the refuted engine no longer shares the premise {shared} with the beta one — the \
             refutation stops bearing on this engine"
        );
    }
}

/// R23 named the gap this rung's interface is built for.
#[test]
fn test_candmodel_r24_follows_r23() {
    let doc = crate::test_utils::flatten_module_doc(include_str!("candmodel_construct_r23.rs"));
    assert!(
        doc.contains("it needs a term typing judgment") || doc.contains("dependent TERM typing"),
        "R23 no longer names the term-judgment gap — R24's premise has moved"
    );
}
