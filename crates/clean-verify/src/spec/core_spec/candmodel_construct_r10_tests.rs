// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Registration battery for R10 of the candidate-model construction ladder.
//!
//! A `#[path]` sibling rather than an inline `mod tests`, exactly as
//! `candmodel_construct_r7_tests.rs` is: the registration half and the battery
//! that reads it back are separate subjects, and the battery is the half that
//! grows with every theorem the rung gains.

use super::super::candmodel_construct_r3::conts_at;
use super::super::candmodel_construct_r5::{ty_apphf_whnf_inv, val_piset_cr3_aux};
use super::*;
use crate::test_utils::parse_check;

/// The theorem table, in registration order. Test-only: the stage below
/// registers each constant with its own description, and this table is what the
/// parse / scratch / re-verification guards iterate.
fn theorem_sources() -> Vec<(String, String, String)> {
    vec![
        (
            "r10_beta_lam_head".to_string(),
            TY_R10_BETA_LAM_HEAD.to_string(),
            VAL_R10_BETA_LAM_HEAD.to_string(),
        ),
        (
            "r10_omegaLam_no_beta".to_string(),
            TY_R10_OMEGALAM_NO_BETA.to_string(),
            val_r10_omegalam_no_beta(),
        ),
        (
            "r10_stuckOmega_delta_none".to_string(),
            ty_r10_stuckomega_delta_none(),
            VAL_R10_STUCKOMEGA_DELTA_NONE.to_string(),
        ),
        (
            "r10_stuckOmega_no_whnf_step".to_string(),
            ty_r10_stuckomega_no_whnf_step(),
            val_r10_stuckomega_no_whnf_step(),
        ),
        (
            "r10_natZero_whnfAcc".to_string(),
            ty_r10_natzero_whnfacc(),
            VAL_R10_NATZERO_WHNFACC.to_string(),
        ),
        (
            "r10_zc_collapse".to_string(),
            ty_r10_zc_collapse(),
            VAL_R10_ZC_COLLAPSE.to_string(),
        ),
        (
            "r10_appStuck_not_whnfAcc".to_string(),
            ty_r10_appstuck_not_whnfacc(),
            val_r10_appstuck_not_whnfacc(),
        ),
        (
            "r10_piSet_cr3_unrestricted_refuted".to_string(),
            ty_r10_piset_cr3_unrestricted_refuted(),
            val_r10_piset_cr3_unrestricted_refuted(),
        ),
        (
            "r10_isCandSet_piSet_refuted".to_string(),
            ty_r10_iscandset_piset_refuted(),
            val_r10_iscandset_piset_refuted(),
        ),
        (
            "r10_cr3_gap_is_real".to_string(),
            ty_r10_cr3_gap_is_real(),
            val_r10_cr3_gap_is_real(),
        ),
        (
            "headInert_app".to_string(),
            TY_HEADINERT_APP.to_string(),
            val_headinert_app(),
        ),
        (
            "headFree_headInert".to_string(),
            TY_HEADFREE_HEADINERT.to_string(),
            VAL_HEADFREE_HEADINERT.to_string(),
        ),
        (
            "inertConst_headInert".to_string(),
            ty_inertconst_headinert(),
            val_inertconst_headinert(),
        ),
        (
            "appIC_beta_inv".to_string(),
            ty_appic_beta_inv(),
            val_appic_beta_inv(),
        ),
        (
            "appIC_whnf_inv".to_string(),
            ty_appic_whnf_inv(),
            val_appic_whnf_inv(),
        ),
        (
            "appHI_whnf_inv".to_string(),
            ty_apphi_whnf_inv(),
            val_apphi_whnf_inv(),
        ),
        (
            "isCandHI_intro".to_string(),
            ty_iscandhi_intro(),
            val_iscandhi_intro(),
        ),
        (
            "isCandHI_cr1".to_string(),
            ty_iscandhi_cr1(),
            val_iscandhi_cr1(),
        ),
        (
            "isCandHI_cr2".to_string(),
            ty_iscandhi_cr2(),
            val_iscandhi_cr2(),
        ),
        (
            "isCandHI_cr3".to_string(),
            ty_iscandhi_cr3(),
            val_iscandhi_cr3(),
        ),
        (
            "isCandHI_weaken".to_string(),
            TY_ISCANDHI_WEAKEN.to_string(),
            VAL_ISCANDHI_WEAKEN.to_string(),
        ),
        (
            "isCandSet_weakenHI".to_string(),
            TY_ISCANDSET_WEAKENHI.to_string(),
            VAL_ISCANDSET_WEAKENHI.to_string(),
        ),
        (
            "isCandHI_whnfAcc".to_string(),
            TY_ISCANDHI_WHNFACC.to_string(),
            VAL_ISCANDHI_WHNFACC.to_string(),
        ),
        (
            "piSet_cr3HI_aux".to_string(),
            ty_piset_cr3hi_aux(),
            val_piset_cr3hi_aux(),
        ),
        (
            "piSet_cr3HI".to_string(),
            ty_piset_cr3hi(),
            val_piset_cr3hi(),
        ),
        (
            "isCandHI_piSet".to_string(),
            TY_ISCANDHI_PISET.to_string(),
            VAL_ISCANDHI_PISET.to_string(),
        ),
        (
            "candInterp_isCandHI".to_string(),
            ty_candinterp_iscandhi(),
            val_candinterp_iscandhi(),
        ),
        (
            "r10_deadConst_headInert".to_string(),
            ty_r10_deadconst_headinert(),
            VAL_R10_DEADCONST_HEADINERT.to_string(),
        ),
        (
            "r10_deadConst_cand_mem".to_string(),
            ty_r10_deadconst_cand_mem(),
            val_r10_deadconst_cand_mem(),
        ),
        (
            "r10_interp_const_pi_witness".to_string(),
            ty_r10_interp_const_pi_witness(),
            val_r10_interp_const_pi_witness(),
        ),
        (
            "r10_headInert_strictly_weaker".to_string(),
            ty_r10_headinert_strictly_weaker(),
            val_r10_headinert_strictly_weaker(),
        ),
        (
            "r10_natRec3_not_headInert".to_string(),
            ty_r10_natrec3_not_headinert(),
            val_r10_natrec3_not_headinert(),
        ),
        (
            "r10_r5_term_excluded".to_string(),
            ty_r10_r5_term_excluded(),
            val_r10_r5_term_excluded(),
        ),
        (
            "r10_counterexample_excluded".to_string(),
            ty_r10_counterexample_excluded(),
            val_r10_counterexample_excluded(),
        ),
        (
            "r10_const_unlock_proper".to_string(),
            ty_r10_const_unlock_proper(),
            val_r10_const_unlock_proper(),
        ),
    ]
}

/// The plain defs and the one inductive, as full declaration sources.
fn decl_sources() -> Vec<(String, String)> {
    vec![
        ("r10_lamTy".to_string(), src_r10_lam_ty()),
        ("r10_lamBody".to_string(), src_r10_lam_body()),
        ("HeadInert".to_string(), src_head_inert()),
        ("candCr3HI".to_string(), src_cand_cr3hi()),
        ("IsCandHI".to_string(), src_is_cand_hi()),
    ]
}

/// Every source in the rung parses as a declaration — microseconds, and it
/// catches the two failure classes that cost whole elaboration cycles
/// (a parenthesised `forall` in argument position, a dropped `fun`).
#[test]
fn test_candmodel_r10_sources_parse() {
    for (name, ty, val) in theorem_sources() {
        let assembled = format!("def {name} : {ty} := {val}");
        parse_check(&assembled)
            .unwrap_or_else(|e| panic!("{name} should parse as a def: {e}\n{assembled}"));
    }
    for (name, src) in decl_sources() {
        parse_check(&src).unwrap_or_else(|e| panic!("{name} should parse: {e}\n{src}"));
    }
}

/// The continuation shapes of the three inversions AGREE with R5's, so the
/// weakened Pi-candidate proof can consume them interchangeably.
#[test]
fn test_candmodel_r10_inversion_shapes_match_r5() {
    assert_eq!(
        ty_apphi_whnf_inv(),
        ty_apphf_whnf_inv().replacen("HeadFree e ->", "HeadInert e ->", 1),
        "the head-inert inversion must be R5's type with only the premise swapped"
    );
    assert!(
        ty_appic_whnf_inv().contains("recmeta_for") && ty_appic_whnf_inv().contains("defval_for"),
        "the inert-const inversion must carry both real-env side conditions"
    );
    assert!(
        !ty_appic_whnf_inv().contains("HeadFree"),
        "the inert-const inversion must not smuggle head-freeness back in"
    );
    // The locally-built continuation binders must render the same types R5
    // quantifies over.
    let rendered = conts_at(&hi_conts("e"), "g2", "");
    for frag in [
        "(kLam : forall (zA : KExpr) (zb : KExpr), Eq KExpr e (KExpr.lam zA zb) -> C)",
        "(kFn : forall (zy : KExpr), beta_reduces e zy -> Eq KExpr g2 (KExpr.app zy a) -> C)",
        "(kArg : forall (zy : KExpr), beta_reduces a zy -> Eq KExpr g2 (KExpr.app e zy) -> C)",
    ] {
        assert!(
            rendered.contains(frag),
            "continuation binders drifted from R5's app_conts: missing {frag}"
        );
    }
}

/// The ONE non-textual site of the weakening is present. R5 can pass its
/// head-free hypothesis straight into the codomain candidate's cr3 at
/// `app e qa0` because `HeadFree` is a `def` over `kapp_fn`; `HeadInert` is
/// an inductive family, so the transport has to be applied. Without this
/// the rung fails at `piSet_cr3HI_aux` with `Discriminant(1) vs
/// Discriminant(4)` — 391 s into a heavy run, which is why it is pinned
/// here at 0.00 s.
#[test]
fn test_candmodel_r10_headinert_transport_is_applied() {
    let aux = val_piset_cr3hi_aux();
    assert!(
        aux.contains("(headInert_app e qa0 hhf)"),
        "piSet_cr3HI_aux must transport head-inertness through the application"
    );
    assert!(
        !aux.contains("(KExpr.app e qa0) hhf "),
        "the bare hypothesis must not survive at the lifted term"
    );
    assert!(
        val_piset_cr3hi_aux()
            != hi_weaken(&val_piset_cr3_aux()).replace("(headInert_app e qa0 hhf)", "hhf"),
        "the transport must be a real difference from R5's text"
    );
}

/// The textual weakening is TOTAL: no head-free spelling survives into the
/// head-inert layer, which is what makes `hi_weaken` sound rather than
/// merely convenient.
#[test]
fn test_candmodel_r10_weakening_is_total() {
    for (name, ty, val) in theorem_sources() {
        if !(name.starts_with("isCandHI_")
            || name.starts_with("piSet_cr3HI")
            || name == "candInterp_isCandHI")
        {
            continue;
        }
        // isCandHI_weaken deliberately mentions the head-free layer: it is
        // the bridge INTO it.
        if name == "isCandHI_weaken" {
            continue;
        }
        for s in [&ty, &val] {
            assert!(
                !s.contains("IsCandHF"),
                "{name} must not mention IsCandHF after weakening"
            );
            assert!(
                !s.contains("candCr3HF"),
                "{name} must not mention candCr3HF after weakening"
            );
            assert!(
                !s.contains("appHF_whnf_inv"),
                "{name} must not call R5's head-free inversion"
            );
        }
    }
}

/// The counterexample is at the REAL environment and is genuinely stuck —
/// the two properties that make it a refutation rather than an anecdote.
#[test]
fn test_candmodel_r10_counterexample_is_real_and_stuck() {
    let ty = ty_r10_piset_cr3_unrestricted_refuted();
    assert!(
        ty.ends_with("-> Empty"),
        "the keystone must be a refutation, not a conditional theorem"
    );
    assert!(
        ty.contains("IsCandHF CA")
            && ty.contains("candStepInv CA CB")
            && ty.contains("candCr3 (PiSet CA CB)"),
        "the refuted statement must carry EVERY side condition isCandHF_piSet asks for"
    );
    let val = val_r10_piset_cr3_unrestricted_refuted();
    assert!(
        val.contains("kcre_name_27") && val.contains("kcre_name_18"),
        "the counterexample must be built from the GENERATED reflected atoms"
    );
    assert!(
        val.contains("r10_stuckOmega_no_whnf_step"),
        "cr3's reduct premise must be discharged by step-freeness, not assumed"
    );
    assert!(
        val_r10_appstuck_not_whnfacc().contains("natRecZ_iota_fires")
            && val_r10_appstuck_not_whnfacc().contains("r5_omegaV_not_whnfAcc"),
        "the divergence must run through the real iota fire and end at the self-loop"
    );
    assert!(
        !ty_r10_appstuck_not_whnfacc().contains("kapp_fn kcre_witness_nat_zero_reduct")
            || val_r10_appstuck_not_whnfacc().contains("r10_beta_lam_head"),
        "the rule RHS must be projected, never transcribed"
    );
}

/// `HeadInert.rec` is consumed with the TWO-binder motive, so a
/// `fixedIndicesToParams` promotion of the leading index would fail loudly
/// rather than silently change the recursor.
#[test]
fn test_candmodel_r10_headinert_recursor_shape() {
    for val in [
        val_headinert_app(),
        val_apphi_whnf_inv(),
        val_r10_natrec3_not_headinert(),
    ] {
        assert!(
            val.contains("HeadInert.rec (fun (ze : KExpr) (_ : HeadInert ze) =>"),
            "HeadInert.rec must be consumed with the two-binder index motive"
        );
    }
    let src = src_head_inert();
    assert!(
        src.contains("| free : forall (e : KExpr)") && src.contains("| inert : forall (n : Name)"),
        "the two constructors must NOT share a leading argument type, or the index is promoted"
    );
}

/// The declarations in REGISTRATION ORDER, driving the scratch elaboration.
fn registration_plan() -> Vec<(&'static str, String, String)> {
    let mut v: Vec<(&'static str, String, String)> = vec![
        ("def", "r10_lamTy".to_string(), src_r10_lam_ty()),
        ("def", "r10_lamBody".to_string(), src_r10_lam_body()),
    ];
    let thm = |name: &str, ty: String, val: String| {
        (
            "thm",
            name.to_string(),
            format!("def {name} : {ty} := {val}"),
        )
    };
    let all = theorem_sources();
    let get = |n: &str| {
        all.iter()
            .find(|(name, _, _)| name == n)
            .map(|(name, ty, val)| thm(name, ty.clone(), val.clone()))
            .unwrap_or_else(|| panic!("{n} should be in theorem_sources()"))
    };
    for n in [
        "r10_beta_lam_head",
        "r10_omegaLam_no_beta",
        "r10_stuckOmega_delta_none",
        "r10_stuckOmega_no_whnf_step",
        "r10_natZero_whnfAcc",
        "r10_zc_collapse",
        "r10_appStuck_not_whnfAcc",
        "r10_piSet_cr3_unrestricted_refuted",
        "r10_isCandSet_piSet_refuted",
        "r10_cr3_gap_is_real",
    ] {
        v.push(get(n));
    }
    v.push(("inductive", "HeadInert".to_string(), src_head_inert()));
    for n in [
        "headInert_app",
        "headFree_headInert",
        "inertConst_headInert",
        "appIC_beta_inv",
        "appIC_whnf_inv",
        "appHI_whnf_inv",
    ] {
        v.push(get(n));
    }
    v.push(("def", "candCr3HI".to_string(), src_cand_cr3hi()));
    v.push(("def", "IsCandHI".to_string(), src_is_cand_hi()));
    for n in [
        "isCandHI_intro",
        "isCandHI_cr1",
        "isCandHI_cr2",
        "isCandHI_cr3",
        "isCandHI_weaken",
        "isCandSet_weakenHI",
        "isCandHI_whnfAcc",
        "piSet_cr3HI_aux",
        "piSet_cr3HI",
        "isCandHI_piSet",
        "candInterp_isCandHI",
        "r10_deadConst_headInert",
        "r10_deadConst_cand_mem",
        "r10_interp_const_pi_witness",
        "r10_headInert_strictly_weaker",
        "r10_natRec3_not_headInert",
        "r10_r5_term_excluded",
        "r10_counterexample_excluded",
        "r10_const_unlock_proper",
    ] {
        v.push(get(n));
    }
    v
}

/// The plan and the source tables name the same constants.
#[test]
fn test_candmodel_r10_plan_matches_registration() {
    let planned: std::collections::BTreeSet<String> =
        registration_plan().into_iter().map(|(_, n, _)| n).collect();
    let mut declared: std::collections::BTreeSet<String> =
        theorem_sources().into_iter().map(|(n, _, _)| n).collect();
    for (n, _) in decl_sources() {
        declared.insert(n);
    }
    assert_eq!(
        planned, declared,
        "registration_plan and the source tables must name the same constants"
    );
}

/// SCRATCH ELABORATION — the iteration tool for this rung.
#[test]
fn test_candmodel_r10_scratch_elaborates() {
    let mut spec = crate::test_utils::build_substitution_spec_with_stack();
    if spec.definitions().contains_key("HeadInert") {
        return;
    }
    let mut failures: Vec<String> = Vec::new();
    for (kind, name, src) in registration_plan() {
        let desc = "R10 scratch candidate";
        let result = match kind {
            "inductive" => spec.add_inductive(&src, desc),
            _ => spec.add_recursive_def(&src, desc),
        };
        if let Err(e) = result {
            failures.push(format!("{name}: {e}"));
        }
    }
    assert!(
        failures.is_empty(),
        "R10 scratch elaboration failures ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// Registration + kernel re-verification against the substitution bundle.
#[test]
fn test_candmodel_r10_registered_and_reverifies() {
    let spec = crate::test_utils::build_substitution_spec_with_stack();
    let mut names: Vec<String> = theorem_sources().into_iter().map(|(n, _, _)| n).collect();
    for (n, _) in decl_sources() {
        names.push(n);
    }
    for name in &names {
        assert!(
            spec.definitions().contains_key(name),
            "{name} should be registered by the candmodel_construct_r10 stage"
        );
    }
    for (name, _, _) in theorem_sources() {
        spec.verify_definition(&name).unwrap_or_else(|e| {
            panic!("{name} should re-typecheck in the spec environment: {e:?}")
        });
    }
}
