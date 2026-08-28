// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R16 tests — derivation irrelevance, the subsingleton theorem it comes from,
//! the two payoffs, their witnesses, and the refusals that measure what the
//! witnesses actually witness.

use super::*;
use crate::test_utils::parse_check;

/// Register R16 into a freshly-built substitution spec if the bundle stage has
/// not already done it. Lets every test below run identically before and after
/// the stage is wired into `bundles.rs`.
fn r16_spec() -> Specification {
    let mut spec = crate::test_utils::build_substitution_spec_with_stack();
    if spec.definitions().contains_key("r16_sval_irrel") {
        return spec;
    }
    spec.add_candmodel_construct_r16()
        .expect("R16 should register into the substitution spec");
    spec
}

/// Parse every generated source. Microseconds, versus a whole spec build.
#[test]
fn test_candmodel_r16_sources_parse() {
    for (name, src) in r16_all_sources() {
        parse_check(&src).unwrap_or_else(|e| panic!("R16 source {name} does not parse: {e}"));
    }
    parse_check(&probe_cross_term()).expect("the cross-term probe must parse");
    parse_check(&probe_irrel_refl()).expect("the Eq.refl probe must parse");
    parse_check(&probe_wrong_shape()).expect("the wrong-shape probe must parse");
}

/// No name registered twice, and the load-bearing ones are all present.
#[test]
fn test_candmodel_r16_names_are_unique() {
    let mut seen = std::collections::BTreeSet::new();
    for (name, _) in r16_all_sources() {
        assert!(seen.insert(name.clone()), "R16 registers {name} twice");
    }
    for required in [
        "r16_wk_shape_unique",
        "r16_wkCastS_refl",
        "r16_wk_inv",
        "r16_wk_deriv_unique",
        "r16_sval_irrel",
        "r16_val_conv",
        "r16_val_step",
        "r16_val_step_star",
        "r16_conv_contrast",
        "r16_deriv_unique_witness",
    ] {
        assert!(seen.contains(required), "R16 lost {required}");
    }
}

/// ITERATION TOOL. Registers the whole table into a substitution spec and
/// reports EVERY failure in one message instead of dying on the first — the
/// R13/R14/R15 pattern, and the reason a rung this size fits in a handful of
/// cycles.
#[test]
fn test_candmodel_r16_scratch_elaborates() {
    let mut spec = crate::test_utils::build_substitution_spec_with_stack();
    if spec.definitions().contains_key("r16_sval_irrel") {
        return;
    }
    let mut failures: Vec<String> = Vec::new();
    for item in r16_items() {
        match item {
            R16Item::Ind { name, src } => {
                if let Err(e) = spec.add_inductive(&src, "r16 scratch") {
                    failures.push(format!("IND {name}: {e}"));
                }
            }
            R16Item::Def { name, src } => {
                if let Err(e) = spec.add_recursive_def(&src, "r16 scratch") {
                    failures.push(format!("DEF {name}: {e}"));
                }
            }
            R16Item::Thm { name, ty, val } => {
                if let Err(e) = add_thm(&mut spec, &name, ty, val, &[], "r16 scratch") {
                    failures.push(format!("THM {name}: {e}"));
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "R16 registration failures ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// Every R16 constant is registered and every theorem re-verifies.
#[test]
fn test_candmodel_r16_registered_and_reverifies() {
    let spec = r16_spec();
    for (name, _) in r16_all_sources() {
        assert!(
            spec.definitions().contains_key(&name)
                || spec
                    .env()
                    .get_const(&clean_kernel::Name::from_string(&name))
                    .is_some(),
            "R16 constant {name} is not registered"
        );
    }
    for item in r16_items() {
        if let R16Item::Thm { name, .. } = item {
            spec.verify_definition(&name)
                .unwrap_or_else(|e| panic!("R16 theorem {name} does not re-verify: {e:?}"));
        }
    }
}

/// The computed-motive type and the transports must delta-unfold. If `r16_wkT`
/// were `Opaque`, `r16_wk_inv`'s result would never expose the continuations and
/// every uniqueness arm would fail; if `r16_wkCastS` were, the reflexive cast
/// would never reduce and the K step could not fire. That is R12's measured
/// elaborator fact, and this asserts the whole spine is reducible.
#[test]
fn test_candmodel_r16_inversion_spine_delta_unfolds() {
    use clean_kernel::{ConstantKind, Name};
    let spec = r16_spec();
    for op in [
        "r16_propUnit",
        "r16_arrCod",
        "r16_shapeOf",
        "r16_wkCastS",
        "r16_wkT",
        "r16_wk_inv",
        "r16_unbox",
        "r16_svalConvTransports",
    ] {
        let c = spec
            .env()
            .get_const(&Name::from_string(op))
            .unwrap_or_else(|| panic!("{op} missing from the R16 environment"));
        assert_eq!(
            c.kind,
            ConstantKind::Definition,
            "{op} must be a reducible Definition; Opaque or Theorem stops the reduction every \
             later R16 proof depends on"
        );
    }
}

/// CENSUS. The computed axiom closure — by kernel ground truth, not by the
/// declared `axiom_deps` field — must be empty for every headline constant.
/// K-like reduction is a kernel REDUCTION RULE, not an axiom, so
/// `r16_wkCastS_refl` and everything above it must show an empty closure.
#[test]
fn test_candmodel_r16_axiom_closure_is_empty() {
    let spec = r16_spec();
    for name in [
        "r16_shape_correct",
        "r16_wk_shape_unique",
        "r16_wkCastS_refl",
        "r16_uniq_var",
        "r16_uniq_sort",
        "r16_pi_align",
        "r16_lam_align",
        "r16_app_align",
        "r16_uniq_pi",
        "r16_uniq_lam",
        "r16_uniq_app",
        "r16_wk_deriv_unique",
        "r16_sval_irrel",
        "r16_val_conv",
        "r16_val_step",
        "r16_val_step_star",
        "r16_sval_conv_transports",
        "r16_conv_contrast",
        "r16_shape_unique_witness",
        "r16_deriv_unique_witness",
        "r16_irrel_witness",
        "r16_val_step_witness",
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

/// CENSUS, by kernel ground truth, over the bundle R16 actually changes.
///
/// `tests/axiom_ratchet.rs::no_new_admitted_axioms_in_spec` is the
/// authoritative gate, but it builds the FULL spec, which the suite state
/// records at **28.87 GB peak RSS**
/// (`data/suite_state/clean-verify__test__axiom_ratchet.json`) — it does not fit
/// on a 16 GB box, exactly as R12-R15 recorded. This is the same
/// `newly_admitted_axioms` subset check run against the substitution bundle,
/// which is the only environment this rung modifies.
#[test]
fn test_candmodel_r16_admits_no_new_census_axiom() {
    let spec = r16_spec();
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
        "R16 newly admitted kernel axioms into the substitution bundle: {newly:?}"
    );
}

/// MEASUREMENT, not a claim. `r16_irrel_witness` is stated at a derivation the
/// kernel cannot unfold (`r15_wk_step_sort` is a theorem, hence `Opaque`), so
/// the equation is NOT `Eq.refl` in disguise. Without this the witness would be
/// compatible with an irrelevance theorem that only ever equated definitionally
/// equal derivations.
#[test]
fn test_candmodel_r16_irrelevance_witness_is_not_definitional() {
    let mut spec = r16_spec();
    assert!(
        spec.add_recursive_def(&probe_irrel_refl(), "negative control")
            .is_err(),
        "the two interpretations are DEFINITIONALLY equal — r16_irrel_witness witnesses nothing, \
         and the K step in r16_wkCastS_refl is not doing the work the rung claims"
    );
}

/// MEASUREMENT of the theorem's scope: derivation uniqueness is about ONE term.
/// Claimed across two different terms — R12's redex and its contractum, which
/// `r12_beta_contractum_is_arg` shows are only PROPOSITIONALLY related — the
/// kernel must refuse.
#[test]
fn test_candmodel_r16_uniqueness_is_not_cross_term() {
    let mut spec = r16_spec();
    assert!(
        spec.add_recursive_def(&probe_cross_term(), "scope control")
            .is_err(),
        "derivation uniqueness typechecked ACROSS TWO TERMS — the statement has lost its subject \
         index and r16_deriv_unique_witness witnesses nothing"
    );
}

/// MEASUREMENT: shape uniqueness really is about the shape the derivation
/// carries. Fed a second shape no derivation of the term has, the kernel refuses.
#[test]
fn test_candmodel_r16_shape_uniqueness_reads_the_derivation() {
    let mut spec = r16_spec();
    assert!(
        spec.add_recursive_def(&probe_wrong_shape(), "shape control")
            .is_err(),
        "r16_wk_shape_unique accepted a derivation at a shape it does not have"
    );
}

/// The rung's structural claim, asserted from its OWN source rather than from
/// prose: the K step is ONE standalone constant, and no other R16 source spells
/// a reflexive-cast elimination inline. If a future edit inlines it as a
/// recursor minor — the ladder's measured elaborator trap — this fails.
#[test]
fn test_candmodel_r16_k_step_is_load_bearing() {
    assert!(
        VAL_WK_CAST_S_REFL.trim().ends_with("Eq.refl (WK D e a) h"),
        "r16_wkCastS_refl is no longer the bare Eq.refl that measures K"
    );
    let users: Vec<String> = r16_all_sources()
        .into_iter()
        .filter(|(n, s)| n.as_str() != "r16_wkCastS_refl" && s.contains("r16_wkCastS_refl"))
        .map(|(n, _)| n)
        .collect();
    assert_eq!(
        users,
        vec![
            "r16_uniq_var".to_string(),
            "r16_uniq_sort".to_string(),
            "r16_pi_align".to_string(),
            "r16_lam_align".to_string(),
        ],
        "the set of constants consuming the K step changed; r16_app_align must NOT be among them \
         (WK.app carries the codomain shape as a bare index, so its alignment needs no cast)"
    );
}

/// The four `KExpr` heads outside `WK`'s reach are discharged by COMPUTATION,
/// and no discrimination or injectivity lemma appears in the inversion — R15's
/// idiom, carried forward and asserted from the source.
#[test]
fn test_candmodel_r16_dead_arms_are_killed_by_computation() {
    let t = src_wk_t();
    assert_eq!(
        t.matches("r16_propUnit").count(),
        4,
        "r16_wkT no longer sends exactly the four non-WK heads (const/let_/proj/lit) to the Prop \
         unit"
    );
    let inv = src_wk_inv();
    for banned in [
        "_ne_app", "_ne_lam", "_ne_pi", "_ne_let", "_ne_proj", "_inj_fst", "_inj_snd",
    ] {
        assert!(
            !inv.contains(banned),
            "r16_wk_inv reintroduced the discrimination scaffold ({banned}); the computed motive \
             is supposed to make it unnecessary"
        );
    }
    assert!(
        !inv.contains("r16_wkCastS_refl"),
        "the inversion itself must not use K — only the alignment lemmas may"
    );
}

/// The contrast is a CONVERSION, not a reduction: the two redexes share a
/// contractum and neither steps to the other. Asserted from the rung's own
/// sources so the claim cannot drift out of the docs.
#[test]
fn test_candmodel_r16_contrast_is_a_real_conversion() {
    assert!(
        src_conv_star1().contains("r12_betaRedex") && src_conv_star2().contains("r16_convRedex2"),
        "the two legs of the join no longer start at the two distinct redexes"
    );
    assert!(
        src_conv_star1().contains(INST0) && src_conv_star2().contains(INST0),
        "the two legs no longer meet at the same reduct"
    );
    assert!(
        VAL_CONV_CONTRAST.contains("r11_candInterp_step_conv_refuted"),
        "r16_conv_contrast no longer carries R11's refutation"
    );
    let spec = r16_spec();
    assert!(
        spec.definitions()
            .contains_key("r11_candInterp_step_conv_refuted"),
        "R11's refutation left the substitution bundle"
    );
}

/// R12's TWO HORNS are about universes and about structural recursion.
/// Derivation irrelevance is neither, exactly as extensionality (R13),
/// substitution (R14) and subject reduction (R15) were neither. Re-asserted from
/// R12's OWN source tables, as R13/R14/R15's tests do.
#[test]
fn test_candmodel_r16_leaves_r12_horns_standing() {
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

/// R15's conditional is DISCHARGED, not restated: `r16_val_conv` must go through
/// `r15_val_conv_from_irrel` and supply `r16_sval_irrel` as its hypothesis.
#[test]
fn test_candmodel_r16_discharges_r15s_conditional() {
    assert!(
        VAL_VAL_CONV.contains("r15_val_conv_from_irrel") && VAL_VAL_CONV.contains("r16_sval_irrel"),
        "r16_val_conv no longer discharges R15's named hypothesis"
    );
    assert!(
        !TY_VAL_CONV.contains("sval D ze zs zh1 zr"),
        "r16_val_conv still carries the irrelevance hypothesis; it is supposed to be unconditional"
    );
    let spec = r16_spec();
    assert!(
        spec.definitions().contains_key("r15_val_conv_from_irrel"),
        "R15's conditional left the substitution bundle"
    );
}

/// The drift-proof premise gate. Derives the name set from R16's OWN table
/// rather than from a hand-written list. The hand-written list in
/// `premise_witness::tests::test_candmodel_ladder_premises_are_witnessed` is the
/// standing-rule record; this is the guard.
#[test]
fn test_candmodel_r16_introduces_no_unwitnessed_premise() {
    let spec = r16_spec();
    let mine: std::collections::BTreeSet<String> =
        r16_all_sources().into_iter().map(|(n, _)| n).collect();
    let live: Vec<String> = crate::premise_witness::unwitnessed_premises(&spec)
        .into_iter()
        .map(|u| u.predicate)
        .filter(|p| mine.contains(p))
        .collect();
    assert!(
        live.is_empty(),
        "R16 assumes predicates nothing concludes: {live:?}"
    );
}
