// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R18 tests — the semantic transfer, the stack carried across it, and the two
//! refusals that measure what the transfer does and where it stops.

use super::super::candmodel_construct_r18_src::{
    probe_lift_at_wkc, probe_transfer_refl, r18_all_sources, r18_items, val_xval_sval,
};
use super::*;
use crate::test_utils::parse_check;

/// Register R18 into a freshly-built substitution spec if the bundle stage has
/// not already done it. Lets every test below run identically before and after
/// the stage is wired into `bundles.rs`.
fn r18_spec() -> Specification {
    let mut spec = crate::test_utils::build_substitution_spec_with_stack();
    if spec.definitions().contains_key("r18_xval_sval") {
        return spec;
    }
    spec.add_candmodel_construct_r18()
        .expect("R18 should register into the substitution spec");
    spec
}

/// Parse every generated source. Microseconds, versus a whole spec build.
#[test]
fn test_candmodel_r18_sources_parse() {
    for (name, src) in r18_all_sources() {
        parse_check(&src).unwrap_or_else(|e| panic!("R18 source {name} does not parse: {e}"));
    }
    parse_check(&probe_transfer_refl()).expect("the Eq.refl probe must parse");
    parse_check(&probe_lift_at_wkc()).expect("the WKC-generalised lift probe must parse");
}

/// No name registered twice, and the load-bearing ones are all present.
#[test]
fn test_candmodel_r18_names_are_unique() {
    let mut seen = std::collections::BTreeSet::new();
    for (name, _) in r18_all_sources() {
        assert!(seen.insert(name.clone()), "R18 registers {name} twice");
    }
    for required in [
        "r18_xval_sval",
        "r18_xval_env_congr",
        "r18_xval_step",
        "r18_xval_step_star",
        "r18_xval_conv",
        "r18_xval_lift",
        "r18_xval_psub",
        "r18_xval_inst",
        "r18_transfer_witness",
        "r18_xval_step_witness",
    ] {
        assert!(seen.contains(required), "R18 lost {required}");
    }
}

/// ITERATION TOOL. Registers the whole table into a substitution spec and
/// reports EVERY failure in one message instead of dying on the first — the
/// R13-R17 pattern, and the reason a rung fits in a handful of cycles.
#[test]
fn test_candmodel_r18_scratch_elaborates() {
    let mut spec = crate::test_utils::build_substitution_spec_with_stack();
    // WIRED-STATE BRANCH, deliberately NOT an early `return`. A bare return is a
    // self-skip: once the rung is in `bundles.rs` this test would report ok
    // forever, including if the stage were later dropped. Assert the rung's whole
    // table is live in the built spec instead, so the wired path carries a claim.
    if spec.definitions().contains_key("r18_xval_sval") {
        for (name, _) in r18_all_sources() {
            assert!(
                spec.env()
                    .get_const(&clean_kernel::Name::from_string(&name))
                    .is_some(),
                "R18 is wired but {name} is absent from the built spec"
            );
        }
    } else {
        let mut failures: Vec<String> = Vec::new();
        for item in r18_items() {
            let R18Item::Thm { name, ty, val } = item;
            if let Err(e) = add_thm(&mut spec, &name, ty, val, &[], "r18 scratch") {
                failures.push(format!("THM {name}: {e}"));
            }
        }
        assert!(
            failures.is_empty(),
            "R18 registration failures ({}):\n{}",
            failures.len(),
            failures.join("\n")
        );
    }
}

/// Every R18 constant is registered and every theorem re-verifies.
#[test]
fn test_candmodel_r18_registered_and_reverifies() {
    let spec = r18_spec();
    for (name, _) in r18_all_sources() {
        assert!(
            spec.definitions().contains_key(&name)
                || spec
                    .env()
                    .get_const(&clean_kernel::Name::from_string(&name))
                    .is_some(),
            "R18 constant {name} is not registered"
        );
        spec.verify_definition(&name)
            .unwrap_or_else(|e| panic!("R18 theorem {name} does not re-verify: {e:?}"));
    }
}

/// CENSUS. The computed axiom closure — by kernel ground truth, not by the
/// declared `axiom_deps` field — must be empty for every R18 constant. The
/// `lam` arm goes through R13's `spec_funext`, whose closure is `Quot.sound`
/// plus the `Quot` type formers; every one of those is in the explicit
/// foundational base, which is exactly why `r14_val_lift` — same route — has
/// shown an empty closure since R14.
#[test]
fn test_candmodel_r18_axiom_closure_is_empty() {
    let spec = r18_spec();
    for (name, _) in r18_all_sources() {
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

/// CENSUS, by kernel ground truth, over the bundle R18 actually changes.
///
/// `tests/axiom_ratchet.rs::no_new_admitted_axioms_in_spec` is the
/// authoritative gate. **It fits on this box, and the figure that said
/// otherwise was false** — measured 2026-09-17: that gate over the FULL spec
/// runs in 18m30s at **2.75 GB peak RSS** under `heavy_gate.sh run 4`. The
/// "28.87 GB peak RSS" this comment used to cite was a CARRIED peak, never a
/// measurement (`_prior_peak_rss_gb` raises a weight and never lowers it), and
/// `docs/archive/CLAUDE_MD_HISTORY.md` had already retracted it. It cited
/// `data/suite_state/clean-verify__test__axiom_ratchet.json`, the very file
/// that refutes it — 2.04 GB over 569 samples. Check the file a sentence
/// cites, not only its number.
///
/// This subset check stays as the FAST per-rung one, against the substitution
/// bundle that is the only environment this rung modifies. It is NOT a
/// substitute for the authoritative gate, which should be run before landing.
#[test]
fn test_candmodel_r18_admits_no_new_census_axiom() {
    let spec = r18_spec();
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
        "R18 newly admitted kernel axioms into the substitution bundle: {newly:?}"
    );
}

/// MEASUREMENT: the transfer is NOT a definitional identity.
///
/// `xval D e s (r17_wk_wkc D e s h) r` is `WKC.rec` stuck on `r17_wk_wkc`
/// stuck on the VARIABLE `h`, and `sval D e s h r` is `WK.rec` stuck on the
/// same variable. Neither reduces, so `Eq.refl` cannot prove the general
/// statement and the kernel must refuse it. Without this control the whole
/// rung could be a restatement.
#[test]
fn test_candmodel_r18_transfer_is_not_definitional() {
    let mut spec = r18_spec();
    assert!(
        spec.add_recursive_def(&probe_transfer_refl(), "negative control")
            .is_err(),
        "the transfer is DEFINITIONAL — r18_xval_sval and every theorem built on it witness \
         nothing"
    );
}

/// THE SCOPE OF GROUP C, made machine-visible.
///
/// `r18_xval_lift` is stated at `h : WK D e s`, so it says nothing about a
/// `konst`- or `let_`-headed `WKC` derivation. This probe is that theorem
/// generalised to an arbitrary `hw : WKC D e s` with the SAME proof term; the
/// kernel must refuse it. The refusal is a telescope mismatch, and the reason
/// it cannot be repaired is the actual content: both ingredients the proof
/// would have to keep — `wk_lift` and `r14_val_lift` — take a `WK` derivation,
/// and at a `konst`- or `let_`-headed `WKC` derivation there is nothing to hand
/// them. If this ever passes, the transferred stack has silently become native
/// and the module doc's scope paragraph is wrong.
#[test]
fn test_candmodel_r18_transferred_stack_does_not_reach_all_of_wkc() {
    let mut spec = r18_spec();
    assert!(
        spec.add_recursive_def(&probe_lift_at_wkc(), "scope control")
            .is_err(),
        "r18_xval_lift's proof went through at an arbitrary WKC derivation — Group C is not \
         scoped to the image of r17_wk_wkc after all, and the module doc is wrong"
    );
}

/// The transfer's arms are the helpers R13/R14 already built, and nothing else.
/// Measured from the rung's OWN source so a later edit that smuggles in a new
/// semantic lemma — or an axiom-shaped escape hatch — fails here rather than
/// quietly widening the trust story.
#[test]
fn test_candmodel_r18_transfer_reuses_only_r13_r14_machinery() {
    let src = val_xval_sval();
    for required in [
        "r14_sval_pi_congr",
        "r14_vapply_congr",
        "r13_vd_arr_funext",
        "WK.rec",
    ] {
        assert!(
            src.contains(required),
            "the transfer no longer goes through {required}"
        );
    }
    for banned in ["sorry", "Classical", "axiom", "candInterp"] {
        assert!(
            !src.contains(banned),
            "the transfer reaches {banned}, which no arm of it may"
        );
    }
}

/// R17's own handoff sentence names this rung's subject. If that sentence ever
/// leaves R17, the two module docs have drifted and the ladder's reading order
/// is broken.
#[test]
fn test_candmodel_r18_closes_the_item_r17_named() {
    let doc = crate::test_utils::flatten_module_doc(include_str!("candmodel_construct_r17.rs"));
    assert!(
        doc.contains("the semantic transfer"),
        "R17 no longer names the semantic transfer as its next item — R18's premise has moved"
    );
}
