// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R17 tests — the constructor gap, the operations carried to it, the surviving
//! subsingleton, the settled conversion-rule question, and the refusals that
//! measure what each witness actually witnesses.

use super::*;
use crate::test_utils::parse_check;

/// Register R17 into a freshly-built substitution spec if the bundle stage has
/// not already done it. Lets every test below run identically before and after
/// the stage is wired into `bundles.rs`.
fn r17_spec() -> Specification {
    let mut spec = crate::test_utils::build_substitution_spec_with_stack();
    if spec.definitions().contains_key("r17_xval_irrel") {
        return spec;
    }
    spec.add_candmodel_construct_r17()
        .expect("R17 should register into the substitution spec");
    spec
}

/// Parse every generated source. Microseconds, versus a whole spec build.
#[test]
fn test_candmodel_r17_sources_parse() {
    for (name, src) in r17_all_sources() {
        parse_check(&src).unwrap_or_else(|e| panic!("R17 source {name} does not parse: {e}"));
    }
    parse_check(&probe_irrel_refl()).expect("the Eq.refl probe must parse");
    parse_check(&probe_zeta_junk()).expect("the junk-valuation probe must parse");
    parse_check(&probe_konst_wrong_shape()).expect("the wrong-shape probe must parse");
    parse_check(&probe_konst_delta_active()).expect("the delta-active probe must parse");
}

/// No name registered twice, and the load-bearing ones are all present.
#[test]
fn test_candmodel_r17_names_are_unique() {
    let mut seen = std::collections::BTreeSet::new();
    for (name, _) in r17_all_sources() {
        assert!(seen.insert(name.clone()), "R17 registers {name} twice");
    }
    for required in [
        "WKC",
        "xval",
        "r17_wkc_shape_unique",
        "r17_wkc_deriv_unique",
        "r17_xval_irrel",
        "wkc_lift",
        "wkc_psub",
        "wkc_inst",
        "wkc_step",
        "r17_xval_zeta",
        "r17_conv_shape_unique",
        "r17_conv_breaks_subsingleton",
        "r17_conv_verdict",
        "r17_unrestricted_konst_refuted",
        "r17_constructor_gap_closed",
    ] {
        assert!(seen.contains(required), "R17 lost {required}");
    }
}

/// ITERATION TOOL. Registers the whole table into a substitution spec and
/// reports EVERY failure in one message instead of dying on the first — the
/// R13-R16 pattern, and the reason a rung this size fits in a handful of cycles.
#[test]
fn test_candmodel_r17_scratch_elaborates() {
    let mut spec = crate::test_utils::build_substitution_spec_with_stack();
    if spec.definitions().contains_key("r17_xval_irrel") {
        return;
    }
    let mut failures: Vec<String> = Vec::new();
    for item in r17_items() {
        match item {
            R17Item::Ind { name, src } => {
                if let Err(e) = spec.add_inductive(&src, "r17 scratch") {
                    failures.push(format!("IND {name}: {e}"));
                }
            }
            R17Item::Def { name, src } => {
                if let Err(e) = spec.add_recursive_def(&src, "r17 scratch") {
                    failures.push(format!("DEF {name}: {e}"));
                }
            }
            R17Item::Thm { name, ty, val } => {
                if let Err(e) = add_thm(&mut spec, &name, ty, val, &[], "r17 scratch") {
                    failures.push(format!("THM {name}: {e}"));
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "R17 registration failures ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// Every R17 constant is registered and every theorem re-verifies.
#[test]
fn test_candmodel_r17_registered_and_reverifies() {
    let spec = r17_spec();
    for (name, _) in r17_all_sources() {
        assert!(
            spec.definitions().contains_key(&name)
                || spec
                    .env()
                    .get_const(&clean_kernel::Name::from_string(&name))
                    .is_some(),
            "R17 constant {name} is not registered"
        );
    }
    for item in r17_items() {
        if let R17Item::Thm { name, .. } = item {
            spec.verify_definition(&name)
                .unwrap_or_else(|e| panic!("R17 theorem {name} does not re-verify: {e:?}"));
        }
    }
}

/// The computed-motive types, the transports, the interpretation and the two
/// discriminators must delta-unfold. R12's measured elaborator fact: an
/// `add_definition` registration lowers to `Opaque` and stops the reduction
/// every later proof depends on.
#[test]
fn test_candmodel_r17_reduction_spine_delta_unfolds() {
    use clean_kernel::{ConstantKind, Name};
    let spec = r17_spec();
    for op in [
        "xval",
        "r17_wk_wkc",
        "r17_notArrT",
        "r17_shapeOf",
        "r17_wkcCastS",
        "r17_wkcCastT",
        "r17_wkcT",
        "r17_wkc_inv",
        "r17_wkcLamT",
        "r17_wkc_lam_inv",
        "wkc_lift",
        "wkc_psub",
        "wkc_inst",
        "wkc_step",
        "r17_const_no_step",
        "r17_wkv_tag",
        "r17_zeroT",
        "r17_convDeriv",
    ] {
        let c = spec
            .env()
            .get_const(&Name::from_string(op))
            .unwrap_or_else(|| panic!("{op} missing from the R17 environment"));
        assert_eq!(
            c.kind,
            ConstantKind::Definition,
            "{op} must be a reducible Definition; Opaque or Theorem stops the reduction every \
             later R17 proof depends on"
        );
    }
}

/// CENSUS. The computed axiom closure — by kernel ground truth, not by the
/// declared `axiom_deps` field — must be empty for every headline constant.
/// Definitional proof irrelevance and K-like reduction are kernel REDUCTION
/// RULES, not axioms, so `r17_uniq_konst` and `r17_wkcCastS_refl` must show an
/// empty closure too.
#[test]
fn test_candmodel_r17_axiom_closure_is_empty() {
    let spec = r17_spec();
    for name in [
        "r17_shape_correct",
        "r17_wkc_shape_unique",
        "r17_shapeOf_agrees_on_wk",
        "r17_lam_never_ty",
        "r17_wkcCastS_refl",
        "r17_uniq_var",
        "r17_uniq_sort",
        "r17_uniq_konst",
        "r17_pi_align",
        "r17_lam_align",
        "r17_app_align",
        "r17_let_align",
        "r17_uniq_pi",
        "r17_uniq_lam",
        "r17_uniq_app",
        "r17_uniq_let",
        "r17_wkc_deriv_unique",
        "r17_xval_irrel",
        "r17_headFree_wkc_arr",
        "r17_headInert_wkc",
        "r17_wkv_shape_correct",
        "r17_conv_shape_unique",
        "r17_conv_breaks_subsingleton",
        "r17_conv_verdict",
        "r17_konst_mem_witness",
        "r17_xval_zeta",
        "r17_deriv_unique_witness",
        "r17_irrel_witness",
        "r17_unrestricted_konst_refuted",
        "r17_constructor_gap_closed",
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

/// CENSUS, by kernel ground truth, over the bundle R17 actually changes.
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
fn test_candmodel_r17_admits_no_new_census_axiom() {
    let spec = r17_spec();
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
        "R17 newly admitted kernel axioms into the substitution bundle: {newly:?}"
    );
}

/// MEASUREMENT, not a claim. `r17_irrel_witness` equates the interpretations of
/// two derivations the kernel cannot identify by computation — R14's `wk_inst`
/// through the embedding, and `wkc_step` through the whole ζ inversion — so the
/// equation is not `Eq.refl` in disguise.
#[test]
fn test_candmodel_r17_irrelevance_witness_is_not_definitional() {
    let mut spec = r17_spec();
    assert!(
        spec.add_recursive_def(&probe_irrel_refl(), "negative control")
            .is_err(),
        "the two interpretations are DEFINITIONALLY equal — r17_irrel_witness witnesses nothing"
    );
}

/// NON-DEGENERACY of the `let_` interpretation clause, both halves. The positive
/// one is the registered `r17_xval_zeta_reads_value`; this is its control — the
/// junk-extended reading is a DIFFERENT value and the kernel must refuse the
/// claim that they agree.
///
/// The spelling of the control is itself measured: with a `sort` value the two
/// readings agree (`xval` sends every sort to the top candidate and
/// `junkD (Sk.kd Sk.ty)` IS the top candidate), and at `r12_betaJunkEnv` they
/// agree whatever the value is. The first version of this test PASSED the probe
/// and therefore measured nothing.
#[test]
fn test_candmodel_r17_zeta_reads_the_value_not_junk() {
    let mut spec = r17_spec();
    assert!(
        spec.definitions().contains_key("r17_xval_zeta_reads_value"),
        "the positive half of the let_ non-degeneracy pair left the rung"
    );
    assert!(
        spec.add_recursive_def(&probe_zeta_junk(), "non-degeneracy control")
            .is_err(),
        "the let_ clause of xval does not read the VALUE — the zeta law is degenerate"
    );
}

/// MEASUREMENT: `WKC.konst` concludes at `Sk.ty` and at NO other shape. Fed the
/// kind shape, the kernel must refuse.
#[test]
fn test_candmodel_r17_konst_shape_is_ty_only() {
    let mut spec = r17_spec();
    assert!(
        spec.add_recursive_def(&probe_konst_wrong_shape(), "shape control")
            .is_err(),
        "WKC.konst accepted a shape other than Sk.ty — r17_headFree_wkc_arr's konst arm, and with \
         it the whole subject-reduction route, is unsound"
    );
}

/// MEASUREMENT: the INERTNESS premise is real. `kcre_witness_delta_head` HAS a
/// definitional value over the live `the_red_env`, so its `defval_for` is not
/// `none` and `Eq.refl` cannot prove the first premise.
#[test]
fn test_candmodel_r17_konst_needs_inertness() {
    let mut spec = r17_spec();
    assert!(
        spec.add_recursive_def(&probe_konst_delta_active(), "inertness control")
            .is_err(),
        "WKC.konst typed a DELTA-ACTIVE constant — the inertness premise is decorative and \
         r17_unrestricted_konst_refuted proves subject reduction is then lost"
    );
}

/// THE CONSTRUCTOR GAP, measured from the rung's OWN source. R16's inversion
/// sent FOUR heads to the Prop unit; R17's sends TWO. If a later edit changes
/// either count, the "gap closed" claim has drifted.
#[test]
fn test_candmodel_r17_dead_arms_drop_from_four_to_two() {
    use super::super::candmodel_construct_r16_src as r16;
    assert_eq!(
        r16::src_wk_t().matches("r16_propUnit").count(),
        4,
        "R16's inversion no longer sends exactly four heads to the Prop unit"
    );
    let t = src_wkc_t();
    assert_eq!(
        t.matches("r16_propUnit").count(),
        2,
        "r17_wkcT no longer sends exactly the two remaining non-WKC heads (proj/lit) to the Prop \
         unit"
    );
    assert!(
        t.contains("KExpr.const qn qus") && t.contains("KExpr.let_ qt qv qb"),
        "r17_wkcT lost a LIVE const or let_ clause"
    );
    for banned in [
        "_ne_app", "_ne_lam", "_ne_pi", "_ne_let", "_ne_proj", "_inj_fst", "_inj_snd",
    ] {
        assert!(
            !src_wkc_inv().contains(banned),
            "r17_wkc_inv reintroduced the discrimination scaffold ({banned}); the computed motive \
             is supposed to make it unnecessary"
        );
    }
}

/// THE CHEAP SURPRISE, asserted from source: `wkc_step` reuses R15's step
/// inversion VERBATIM in five arms, R1's `let` inversion in one and the const
/// refutation in one — and R10's `HeadInert` inversion machinery appears
/// NOWHERE in it.
#[test]
fn test_candmodel_r17_subject_reduction_reuses_r15() {
    let s = src_wkc_step();
    assert_eq!(
        s.matches("r15_whnf_stepT_inv").count(),
        5,
        "wkc_step no longer reuses R15's step inversion in exactly the five old arms"
    );
    assert_eq!(
        s.matches("letRedex_whnf_inv").count(),
        1,
        "wkc_step's let_ arm no longer goes through R1's zeta-redex inversion"
    );
    assert_eq!(
        s.matches("r17_const_no_step").count(),
        1,
        "wkc_step's konst arm is no longer a refutation"
    );
    assert!(
        !s.contains("appHI_whnf_inv") && !s.contains("HeadInert"),
        "wkc_step now needs R10's HeadInert inversion; the r17_headFree_wkc_arr route (konst \
         concludes at Sk.ty, WKC.app's function premise is at an arrow) has been lost"
    );
    assert_eq!(
        s.matches("wkc_inst").count(),
        2,
        "head-beta and zeta must BOTH land on wkc_inst — that is what the let_ rule's \
         value-shaped binder slot was chosen for"
    );
}

/// The K step stays quarantined, and the two cast-free alignments stay cast-free.
#[test]
fn test_candmodel_r17_k_step_is_load_bearing() {
    assert!(
        VAL_WKC_CAST_S_REFL
            .trim()
            .ends_with("Eq.refl (WKC D e a) h"),
        "r17_wkcCastS_refl is no longer the bare Eq.refl that measures K"
    );
    let users: Vec<String> = r17_all_sources()
        .into_iter()
        .filter(|(n, s)| n.as_str() != "r17_wkcCastS_refl" && s.contains("r17_wkcCastS_refl"))
        .map(|(n, _)| n)
        .collect();
    assert_eq!(
        users,
        vec![
            "r17_uniq_var".to_string(),
            "r17_uniq_sort".to_string(),
            "r17_uniq_konst".to_string(),
            "r17_pi_align".to_string(),
            "r17_lam_align".to_string(),
        ],
        "the set of constants consuming the K step changed; r17_app_align and r17_let_align must \
         NOT be among them — both carry the conclusion shape as a bare index and need no cast"
    );
}

/// TWO ELABORATOR FACTS THIS RUNG MEASURED, pinned so a re-spelling cannot
/// silently lose them.
///
/// 1. R14's position dependence recurs: the `konst` proof-irrelevance step is a
///    STANDALONE `add_recursive_def` that `r17_uniq_konst` APPLIES. Written
///    inline as a continuation body the elaborator refuses with an `fvar`
///    mismatch.
/// 2. `WKV.rec` is PARAMETER-PROMOTED and `WKC.rec` is not. `WKV.conv` recurses
///    at the SAME shape environment, so `fixedIndicesToParams` fires; `WKC.pi` /
///    `WKC.lam` / `WKC.let_` all recurse at `skcons ... D`, so it cannot.
#[test]
fn test_candmodel_r17_wkv_recursor_is_parameter_promoted() {
    assert!(
        src_konst_irrel().contains(":= Eq.refl "),
        "the konst irrelevance step is no longer the bare Eq.refl that measures proof irrelevance"
    );
    assert!(
        val_uniq_konst().contains("r17_konst_irrel D n us zhd zhr hd hr"),
        "r17_uniq_konst no longer APPLIES the standalone irrelevance constant; inlining it is the \
         measured elaborator refusal (fvar mismatch)"
    );
    assert!(
        VAL_WKV_SHAPE_CORRECT.contains("WKV.rec D (fun (qe : KExpr)")
            && SRC_WKV_TAG.contains("WKV.rec D (fun (qe : KExpr)"),
        "WKV.rec is no longer spelled parameter-promoted (D before the motive, three-binder \
         motive) — WKV.conv recurses at the SAME shape environment, so fixedIndicesToParams fires"
    );
    assert!(
        src_wkc_inv().contains("WKC.rec (fun (qD : Nat -> Sk) (qe : KExpr)"),
        "WKC.rec is no longer spelled UNpromoted (four-binder motive taking qD) — WKC escapes the \
         promotion only because pi/lam/let_ recurse at skcons ... D"
    );
}

/// The conversion-rule verdict, asserted from source so it cannot drift into
/// prose: the positive half is about SHAPES and the refutation is about
/// DERIVATIONS, at the FINEST shape relation there is.
#[test]
fn test_candmodel_r17_conv_verdict_is_at_the_finest_relation() {
    assert!(
        SRC_WKV.contains("Eq Sk s1 s2 -> WKV D e s2"),
        "the conv probe no longer uses propositional EQUALITY of shapes; a coarser relation makes \
         the refutation weaker, not stronger"
    );
    assert!(
        VAL_CONV_VERDICT.contains("r17_conv_shape_unique")
            && VAL_CONV_VERDICT.contains("r17_conv_breaks_subsingleton"),
        "r17_conv_verdict no longer carries both halves of the settled answer"
    );
    let spec = r17_spec();
    assert!(
        spec.definitions().contains_key("r16_wk_deriv_unique"),
        "R16's subsingleton left the substitution bundle"
    );
}

/// R12's TWO HORNS are about universes and about structural recursion. The
/// constructor gap is neither, exactly as extensionality (R13), substitution
/// (R14), subject reduction (R15) and derivation irrelevance (R16) were neither.
/// Re-asserted from R12's OWN source tables, as R13-R16's tests do.
#[test]
fn test_candmodel_r17_leaves_r12_horns_standing() {
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
    let xval = src_xval();
    let xbody = xval.split(":=").nth(1).expect("xval has a body");
    assert!(
        !xbody.contains("xval"),
        "HORN 2 applies to xval too: its body became self-referential"
    );
}

/// R10's `cr3` refutation and R11's `candInterp` conversion refutation stand,
/// and this rung re-asserts them from the live bundle rather than from prose.
#[test]
fn test_candmodel_r17_keeps_the_earlier_refutations() {
    let spec = r17_spec();
    for name in [
        "r10_cr3_gap_is_real",
        "r11_candInterp_step_conv_refuted",
        "r16_conv_contrast",
        "r16_val_conv",
    ] {
        assert!(
            spec.definitions().contains_key(name)
                || spec
                    .env()
                    .get_const(&clean_kernel::Name::from_string(name))
                    .is_some(),
            "{name} left the substitution bundle"
        );
    }
}

/// The drift-proof premise gate. Derives the name set from R17's OWN table
/// rather than from a hand-written list. The hand-written list in
/// `premise_witness::tests::test_candmodel_ladder_premises_are_witnessed` is the
/// standing-rule record; this is the guard.
#[test]
fn test_candmodel_r17_introduces_no_unwitnessed_premise() {
    let spec = r17_spec();
    let mine: std::collections::BTreeSet<String> =
        r17_all_sources().into_iter().map(|(n, _)| n).collect();
    let live: Vec<String> = crate::premise_witness::unwitnessed_premises(&spec)
        .into_iter()
        .map(|u| u.predicate)
        .filter(|p| mine.contains(p))
        .collect();
    assert!(
        live.is_empty(),
        "R17 assumes predicates nothing concludes: {live:?}"
    );
}
