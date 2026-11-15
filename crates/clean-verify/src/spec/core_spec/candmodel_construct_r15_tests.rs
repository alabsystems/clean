// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R15 tests — subject reduction, the six `val_step` arms, the fused theorem,
//! their witnesses, and the refusals that measure what `wk_step` preserves.

use super::*;
use crate::test_utils::parse_check;

/// Register R15 into a freshly-built substitution spec if the bundle stage has
/// not already done it. Lets every test below run identically before and after
/// the stage is wired into `bundles.rs`.
fn r15_spec() -> Specification {
    let mut spec = crate::test_utils::build_substitution_spec_with_stack();
    if spec.definitions().contains_key("wk_step") {
        return spec;
    }
    spec.add_candmodel_construct_r15()
        .expect("R15 should register into the substitution spec");
    spec
}

/// Parse every generated source. Microseconds, versus a whole spec build.
#[test]
fn test_candmodel_r15_sources_parse() {
    for (name, src) in r15_all_sources() {
        parse_check(&src).unwrap_or_else(|e| panic!("R15 source {name} does not parse: {e}"));
    }
    parse_check(&probe_wk_step_wrong_shape()).expect("the wrong-shape probe must parse");
    parse_check(&probe_wk_step_at_let()).expect("the let_-subject probe must parse");
}

/// No name registered twice, and the load-bearing ones are all present.
#[test]
fn test_candmodel_r15_names_are_unique() {
    let mut seen = std::collections::BTreeSet::new();
    for (name, _) in r15_all_sources() {
        assert!(seen.insert(name.clone()), "R15 registers {name} twice");
    }
    for required in [
        "r15_headFree_wk",
        "r15_stepT",
        "r15_whnf_stepT_inv",
        "wk_step",
        "r15_val_step_piA",
        "r15_val_step_piB",
        "r15_val_step_lamA",
        "r15_val_step_lamB",
        "r15_val_step_appL",
        "r15_val_step_appR",
        "r15_val_step_sem",
        "r15_val_conv_from_irrel",
    ] {
        assert!(seen.contains(required), "R15 lost {required}");
    }
}

/// ITERATION TOOL. Registers the whole table into a substitution spec and
/// reports EVERY failure in one message instead of dying on the first — the
/// R13/R14 pattern, and the reason a rung this size fits in a handful of
/// cycles.
#[test]
fn test_candmodel_r15_scratch_elaborates() {
    let mut spec = crate::test_utils::build_substitution_spec_with_stack();
    if spec.definitions().contains_key("wk_step") {
        return;
    }
    let mut failures: Vec<String> = Vec::new();
    for item in r15_items() {
        match item {
            R15Item::Def { name, src } => {
                if let Err(e) = spec.add_recursive_def(&src, "r15 scratch") {
                    failures.push(format!("DEF {name}: {e}"));
                }
            }
            R15Item::Thm { name, ty, val } => {
                if let Err(e) = add_thm(&mut spec, &name, ty, val, &[], "r15 scratch") {
                    failures.push(format!("THM {name}: {e}"));
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "R15 registration failures ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// Every R15 constant is registered and every theorem re-verifies.
#[test]
fn test_candmodel_r15_registered_and_reverifies() {
    let spec = r15_spec();
    for (name, _) in r15_all_sources() {
        assert!(
            spec.definitions().contains_key(&name),
            "R15 constant {name} is not registered"
        );
    }
    for item in r15_items() {
        if let R15Item::Thm { name, .. } = item {
            spec.verify_definition(&name)
                .unwrap_or_else(|e| panic!("R15 theorem {name} does not re-verify: {e:?}"));
        }
    }
}

/// The computed-motive types and `wk_step` itself must delta-unfold. If
/// `r15_stepT` were registered `Opaque`, `r15_whnf_stepT_inv`'s result would
/// never expose the continuations and every arm of `wk_step` would fail; if
/// `wk_step` were `Opaque`, no later rung could reduce through subject
/// reduction. That is R12's measured elaborator fact, and this asserts the
/// whole spine is reducible.
#[test]
fn test_candmodel_r15_inversion_types_delta_unfold() {
    use clean_kernel::{ConstantKind, Name};
    let spec = r15_spec();
    for op in [
        "r15_stepT",
        "r15_wkLamT",
        "r15_wk_lam_inv",
        "wk_step",
        "r15_svalLamT",
        "r15_sval_lam_inv",
        "r15_svalStepTransports",
    ] {
        let c = spec
            .env()
            .get_const(&Name::from_string(op))
            .unwrap_or_else(|| panic!("{op} missing from the R15 environment"));
        assert_eq!(
            c.kind,
            ConstantKind::Definition,
            "{op} must be a reducible Definition; Opaque or Theorem stops the reduction every \
             later R15 proof depends on"
        );
    }
}

/// CENSUS. The computed axiom closure — by kernel ground truth, not by the
/// declared `axiom_deps` field — must be empty for every headline constant.
#[test]
fn test_candmodel_r15_axiom_closure_is_empty() {
    let spec = r15_spec();
    for name in [
        "r15_headFree_wk",
        "r15_beta_stepT_inv",
        "r15_whnf_stepT_inv",
        "r15_val_step_piA",
        "r15_val_step_piB",
        "r15_val_step_lamA",
        "r15_val_step_lamB",
        "r15_val_step_appL",
        "r15_val_step_appR",
        "r15_val_step_sem",
        "r15_val_star_sem",
        "r15_sval_transports_any_step",
        "r15_sval_transports_star",
        "r15_sval_transports_congr_step",
        "r15_piCongr_step",
        "r15_val_conv_from_irrel",
        "r15_conv_contrast",
        "r15_wk_step_sort",
        "r15_step_transport_witness",
    ] {
        let closure = crate::spec_axiom_closure::computed_axiom_closure(&spec, name);
        assert!(
            closure.is_empty(),
            "{name} rests on non-foundational axioms: {closure:?}"
        );
        let markers = crate::spec_axiom_closure::computed_trust_markers(&spec, name);
        assert!(
            markers.is_empty(),
            "{name} reaches a trust marker: {markers:?}"
        );
    }
}

/// CENSUS, by kernel ground truth, over the bundle R15 actually changes.
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
fn test_candmodel_r15_admits_no_new_census_axiom() {
    let spec = r15_spec();
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
        "R15 newly admitted kernel axioms into the substitution bundle: {newly:?}"
    );
}

/// MEASUREMENT, not a claim. `wk_step` PRESERVES the shape, and the kernel
/// REFUSES the same reduction claimed at a different one. Without this,
/// `r15_wk_step_sort` would be compatible with a `wk_step` that returned a
/// derivation at whatever shape the caller asked for.
#[test]
fn test_candmodel_r15_subject_reduction_preserves_the_shape() {
    let mut spec = r15_spec();
    assert!(
        spec.add_recursive_def(&probe_wk_step_wrong_shape(), "negative control")
            .is_err(),
        "the reduct's derivation typechecked at a DIFFERENT shape — wk_step is not preserving the \
         shape and r15_wk_step_sort witnesses nothing"
    );
}

/// MEASUREMENT of the rung's own scope: `WK` does not reach `KExpr.let_`, so
/// there is no subject-reduction statement to make there at all. The probe
/// claims a `let_` is shape-typed and the kernel refuses it — which is exactly
/// why the ζ / `let_ty` / `let_val` / `let_body` arms of `beta_reduces` are
/// discharged by `ConstFreeUnit.triv` in `r15_beta_stepT_inv` rather than
/// proved.
#[test]
fn test_candmodel_r15_wk_does_not_reach_let() {
    let mut spec = r15_spec();
    assert!(
        spec.add_recursive_def(&probe_wk_step_at_let(), "scope control")
            .is_err(),
        "WK typed a let_ — the shape system's five-constructor reach has changed and R15's dead \
         arms are no longer dead"
    );
}

/// The rung's structural claim, asserted from its OWN source rather than from
/// prose: every dead arm of the fifteen is discharged by computation
/// (`ConstFreeUnit.triv`), and NO discrimination or injectivity lemma appears
/// anywhere in the step inversion. If a future edit re-introduces the
/// `beta_inv_body` scaffold here, this fails.
#[test]
fn test_candmodel_r15_dead_arms_are_killed_by_computation() {
    let inv = val_beta_step_inv();
    assert!(
        inv.contains("ConstFreeUnit.triv"),
        "the dead arms no longer discharge by computation"
    );
    for banned in [
        "_ne_app", "_ne_lam", "_ne_pi", "_ne_let", "_ne_proj", "_inj_fst", "_inj_snd",
    ] {
        assert!(
            !inv.contains(banned),
            "r15_beta_stepT_inv reintroduced the discrimination scaffold ({banned}); the computed \
             motive is supposed to make it unnecessary"
        );
    }
    assert!(
        val_headfree_wk().matches("Eq.refl").count() >= 4,
        "r15_headFree_wk's four non-app arms are no longer Eq.refl"
    );
}

/// `lamA` is `Eq.refl` and takes NO semantic hypothesis — the domain annotation
/// is semantically inert in `sval`. Asserted from the rung's own table so the
/// claim cannot drift out of the docs.
#[test]
fn test_candmodel_r15_lam_annotation_is_semantically_inert() {
    assert!(
        val_val_step_lama().contains("Eq.refl"),
        "r15_val_step_lamA is no longer definitional"
    );
    assert!(
        !ty_val_step_lama().contains("-> Eq (VD (Sk.arr"),
        "r15_val_step_lamA grew a hypothesis; the annotation is no longer inert"
    );
    let _ = r15_spec();
}

/// R12's TWO HORNS are about universes and about structural recursion. Subject
/// reduction is neither, exactly as extensionality (R13) and substitution (R14)
/// were neither. Re-asserted from R12's OWN source tables, as R13's and R14's
/// tests do.
#[test]
fn test_candmodel_r15_leaves_r12_horns_standing() {
    use super::super::candmodel_construct_r12_src as r12;
    assert!(
        r12::SRC_PI_CAND_V.contains(": KExpr -> Type 1 :="),
        "HORN 1 (predicativity) no longer reads as one universe up"
    );
    let sval = r12::src_sval();
    let body = sval.split(":=").nth(1).expect("sval has a body");
    assert!(
        !body.contains("sval"),
        "HORN 2 (the recursion horn) no longer holds: sval's body became self-referential"
    );
}

/// R11's refutation is RE-ASSERTED, not repaired. `r15_conv_contrast` pairs it
/// with this rung's positive result in one constant, and this test pins that
/// the negative half is still R11's own constant.
#[test]
fn test_candmodel_r15_reasserts_r11_refutation() {
    assert!(
        VAL_CONV_CONTRAST.contains("r11_candInterp_step_conv_refuted"),
        "r15_conv_contrast no longer carries R11's refutation"
    );
    let spec = r15_spec();
    assert!(
        spec.definitions()
            .contains_key("r11_candInterp_step_conv_refuted"),
        "R11's refutation left the substitution bundle"
    );
}

/// The drift-proof premise gate. Derives the name set from R15's OWN table
/// rather than from a hand-written list. The hand-written list in
/// `premise_witness::tests::test_candmodel_ladder_premises_are_witnessed` is the
/// standing-rule record; this is the guard.
#[test]
fn test_candmodel_r15_introduces_no_unwitnessed_premise() {
    let spec = r15_spec();
    let mine: std::collections::BTreeSet<String> =
        r15_all_sources().into_iter().map(|(n, _)| n).collect();
    let live: Vec<String> = crate::premise_witness::unwitnessed_premises(&spec)
        .into_iter()
        .map(|u| u.predicate)
        .filter(|p| mine.contains(p))
        .collect();
    assert!(
        live.is_empty(),
        "R15 assumes predicates nothing concludes: {live:?}"
    );
}
