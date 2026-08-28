// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Registration battery for R11 of the candidate-model construction ladder.
//!
//! A `#[path]` sibling rather than an inline `mod tests`, exactly as
//! `candmodel_construct_r10_tests.rs` is: the registration half and the battery
//! that reads it back are separate subjects, and the battery is the half that
//! grows with every theorem the rung gains.

use super::super::candmodel_construct_r9::{src_syn_ty_c, val_syntyc_fundamental};
use super::*;
use crate::test_utils::parse_check;

/// The theorem table, in registration order. Test-only: the stage below
/// registers each constant with its own description, and this table is what the
/// parse / scratch / re-verification guards iterate.
fn theorem_sources() -> Vec<(String, String, String)> {
    vec![
        (
            "synTyP_fundamental".to_string(),
            ty_syntyp_fundamental(),
            val_syntyp_fundamental(),
        ),
        (
            "synTyP_sn_subst".to_string(),
            ty_syntyp_sn_subst(),
            val_syntyp_sn_subst(),
        ),
        ("synTyP_sn".to_string(), ty_syntyp_sn(), val_syntyp_sn()),
        (
            "synTyP_sn_closed".to_string(),
            ty_syntyp_sn_closed(),
            val_syntyp_sn_closed(),
        ),
        (
            "synTyC_to_synTyP".to_string(),
            TY_SYNTYC_TO_SYNTYP.to_string(),
            val_syntyc_to_syntyp(),
        ),
        (
            "synTyC_sn_via_synTyP".to_string(),
            TY_SYNTYC_SN_VIA_SYNTYP.to_string(),
            VAL_SYNTYC_SN_VIA_SYNTYP.to_string(),
        ),
        (
            "synTyC_no_const_at_pi".to_string(),
            TY_SYNTYC_NO_CONST_AT_PI.to_string(),
            val_syntyc_no_const_at_pi(),
        ),
        ("synTyP_id".to_string(), ty_synty_p_id(), val_synty_p_id()),
        (
            "synTyP_sort_witness".to_string(),
            ty_synty_p_sort_witness(),
            val_synty_p_sort_witness(),
        ),
        (
            "synTyP_konst_pi_witness".to_string(),
            ty_synty_p_konst_pi_witness(),
            val_synty_p_konst_pi_witness(),
        ),
        (
            "synTyP_sn_konst_pi_witness".to_string(),
            ty_synty_p_sn_konst_pi_witness(),
            val_synty_p_sn_konst_pi_witness(),
        ),
        (
            "synTyP_convI_witness".to_string(),
            ty_synty_p_convi_witness(),
            val_synty_p_convi_witness(),
        ),
        (
            "synTyP_sn_convI_witness".to_string(),
            ty_synty_p_sn_convi_witness(),
            val_synty_p_sn_convi_witness(),
        ),
        (
            "r11_synTyP_unlift_type".to_string(),
            TY_R11_SYNTYP_UNLIFT_TYPE.to_string(),
            VAL_R11_SYNTYP_UNLIFT_TYPE.to_string(),
        ),
        (
            "r11_synTyP_lift_type".to_string(),
            TY_R11_SYNTYP_LIFT_TYPE.to_string(),
            VAL_R11_SYNTYP_LIFT_TYPE.to_string(),
        ),
        (
            "synTyP_not_total".to_string(),
            ty_synty_p_not_total(),
            val_synty_p_not_total(),
        ),
        (
            "r11_const_pi_rule_proper".to_string(),
            ty_r11_const_pi_rule_proper(),
            val_r11_const_pi_rule_proper(),
        ),
        (
            "r11_conv_type_defeq".to_string(),
            ty_r11_conv_type_defeq(),
            val_r11_conv_type_defeq(),
        ),
        (
            "r11_candInterp_top_at_app".to_string(),
            TY_R11_CANDINTERP_TOP_AT_APP.to_string(),
            VAL_R11_CANDINTERP_TOP_AT_APP.to_string(),
        ),
        (
            "r11_conv_top_proper_incompatible".to_string(),
            ty_r11_conv_top_proper_incompatible(),
            val_r11_conv_top_proper_incompatible(),
        ),
        (
            "r11_candInterp_conv_refuted".to_string(),
            TY_R11_CANDINTERP_CONV_REFUTED.to_string(),
            val_r11_candinterp_conv_refuted(),
        ),
        (
            "r11_candInterp_conv_eq_refuted".to_string(),
            TY_R11_CANDINTERP_CONV_EQ_REFUTED.to_string(),
            VAL_R11_CANDINTERP_CONV_EQ_REFUTED.to_string(),
        ),
        (
            "r11_candInterp_step_conv_refuted".to_string(),
            TY_R11_CANDINTERP_STEP_CONV_REFUTED.to_string(),
            val_r11_candinterp_step_conv_refuted(),
        ),
        (
            "r11_conv_gap_is_real".to_string(),
            ty_r11_conv_gap_is_real(),
            val_r11_conv_gap_is_real(),
        ),
        (
            "r11_interpEq_conv".to_string(),
            TY_R11_INTERPEQ_CONV.to_string(),
            VAL_R11_INTERPEQ_CONV.to_string(),
        ),
    ]
}

/// The plain defs and the one inductive, as full declaration sources.
fn decl_sources() -> Vec<(String, String)> {
    vec![
        ("SynTyP".to_string(), src_syn_ty_p()),
        (
            "kexpr_is_const_b".to_string(),
            SRC_KEXPR_IS_CONST_B.to_string(),
        ),
        ("r11_pi_discr".to_string(), SRC_R11_PI_DISCR.to_string()),
    ]
}

/// Every source in the rung parses as a declaration — microseconds, and it
/// catches the two failure classes that cost whole elaboration cycles
/// (a parenthesised `forall` in argument position, a dropped `fun`).
#[test]
fn test_candmodel_r11_sources_parse() {
    for (name, ty, val) in theorem_sources() {
        let assembled = format!("def {name} : {ty} := {val}");
        parse_check(&assembled)
            .unwrap_or_else(|e| panic!("{name} should parse as a def: {e}\n{assembled}"));
    }
    for (name, src) in decl_sources() {
        parse_check(&src).unwrap_or_else(|e| panic!("{name} should parse: {e}\n{src}"));
    }
}

/// The eight shared rules are R9's, TEXTUALLY — the whole point of building
/// `SynTyP` by weakening rather than by retyping. If this drifts, the bridge
/// stops being eight one-line constructor rebuilds.
#[test]
fn test_candmodel_r11_shared_rules_are_r9s() {
    let src = src_syn_ty_p();
    let base = p_weaken(&src_syn_ty_c());
    assert!(
        src.starts_with(&base),
        "SynTyP must extend R9's eight rules verbatim, not restate them"
    );
    for rule in [
        "| var :",
        "| sort :",
        "| pi :",
        "| app :",
        "| lam :",
        "| letTy :",
        "| konstDead :",
        "| konstDelta :",
    ] {
        assert!(src.contains(rule), "SynTyP lost R9's {rule} rule");
    }
    assert!(
        !src.contains("SynTyC"),
        "no SynTyC spelling may survive into SynTyP's own source"
    );
    // The two NEW rules, and their order: konstInert then convI, because the
    // fundamental theorem splices its two minors in exactly that order.
    let ki = src.find("| konstInert :").expect("konstInert rule");
    let ci = src.find("| convI :").expect("convI rule");
    assert!(ki > src.find("| konstDelta :").expect("konstDelta"));
    assert!(ci > ki, "convI must be the LAST constructor");
}

/// The const rule keeps BOTH real-environment side conditions. Dropping the
/// recmeta one admits a recursor head at a Pi type, which is exactly R10's
/// counterexample class; dropping the defval one admits a live delta redex.
#[test]
fn test_candmodel_r11_const_rule_keeps_both_side_conditions() {
    let src = src_syn_ty_p();
    let rule = &src[src.find("| konstInert :").expect("konstInert rule")..];
    let rule = &rule[..rule.find("| convI :").expect("convI rule")];
    assert!(
        rule.contains("defval_for (red_def the_red_env) c"),
        "konstInert must demand delta-deadness at the REAL environment"
    );
    assert!(
        rule.contains("recmeta_for (red_rec the_red_env) c"),
        "konstInert must demand non-recursor-hood at the REAL environment"
    );
    assert!(
        rule.contains("SynTyP G (KExpr.const c us) A"),
        "konstInert must conclude at an ARBITRARY type A, or it is R9's konstDead again"
    );
}

/// The fundamental theorem is R9's term with two minors spliced in front of the
/// recursor's indices — never a retyped eight-arm proof. The splice point is
/// R9's own trailing ` G e T h`, so if R9's shape moves this fails loudly here
/// rather than 400 s into a heavy run.
#[test]
fn test_candmodel_r11_fundamental_splices_r9() {
    let base = p_weaken(&val_syntyc_fundamental());
    assert!(
        base.ends_with(" G e T h"),
        "R9's fundamental theorem must still end at the recursor's indices and major premise"
    );
    let val = val_syntyp_fundamental();
    let head = base.strip_suffix(" G e T h").expect("checked above");
    assert!(
        val.starts_with(head),
        "the R11 fundamental theorem must begin with R9's eight-minor prefix, unedited"
    );
    assert!(
        val.contains("r10_deadConst_cand_mem (candInterp qA) (candInterp_isCandHI qA)"),
        "the konstInert arm must go through R10's membership lemma at the interpretation"
    );
    assert!(
        val.contains("(fun (qF : KExpr -> Type) => qF (psubst qs qe))"),
        "the convI arm must transport at the POINTWISE motive"
    );
    assert!(
        !val.contains("SynTyC"),
        "no SynTyC spelling may survive into the R11 fundamental theorem"
    );
}

/// ZERO carried premises on the capstone chain — the invariant R6-R10 all
/// guard, restated at this rung's four statements and at `SynTyP`'s own source.
#[test]
fn test_candmodel_r11_capstones_carry_no_premises() {
    let statements = [
        ty_syntyp_fundamental(),
        ty_syntyp_sn_subst(),
        ty_syntyp_sn(),
        ty_syntyp_sn_closed(),
        src_syn_ty_p(),
        TY_SYNTYC_TO_SYNTYP.to_string(),
    ];
    for s in &statements {
        for banned in [
            "CandModel",
            "RecEnvClosed",
            "RecEnvLiftClosed",
            "DefEnvClosed",
            "EnvAcyclic",
            "red_env_good",
        ] {
            assert!(
                !s.contains(banned),
                "the R11 capstone chain must not carry {banned}: {s}"
            );
        }
    }
}

/// THE SETTLEMENT IS A REFUTATION, not a conditional theorem, and it is stated
/// at `DefEq` — the relation `TypingCtxConv.conv` actually converts along.
#[test]
fn test_candmodel_r11_conversion_is_refuted() {
    for ty in [
        TY_R11_CANDINTERP_CONV_REFUTED.to_string(),
        TY_R11_CANDINTERP_CONV_EQ_REFUTED.to_string(),
        TY_R11_CANDINTERP_STEP_CONV_REFUTED.to_string(),
    ] {
        assert!(
            ty.ends_with("-> Empty"),
            "each conversion statement must be a refutation: {ty}"
        );
    }
    assert!(
        TY_R11_CANDINTERP_CONV_REFUTED.contains("DefEq A B"),
        "the headline refutation must be stated at DefEq"
    );
    assert!(
        TY_R11_CANDINTERP_CONV_EQ_REFUTED.contains("Eq (KExpr -> Type)"),
        "the equality form must equate the two membership PREDICATES (PiSet is contravariant)"
    );
    // The specific refutation is an INSTANCE of the abstract incompatibility,
    // never a second hand-built counterexample.
    let val = val_r11_candinterp_conv_refuted();
    assert!(
        val.contains("r11_conv_top_proper_incompatible candInterp"),
        "the candInterp refutation must instantiate the abstract statement"
    );
    assert!(
        ty_r11_conv_top_proper_incompatible().starts_with("forall (I : KExpr -> KExpr -> Type)"),
        "the abstract statement must quantify over the interpretation"
    );
}

/// The counterexample's type is a genuine type-level BETA REDEX whose head
/// former is `app` and whose contractum's is `pi` — the two formers
/// `candInterp` treats differently. Without that the refutation would not be
/// about conversion at all.
#[test]
fn test_candmodel_r11_counterexample_is_a_type_level_redex() {
    assert!(
        CONV_REDEX.starts_with("(KExpr.app (KExpr.lam "),
        "the refuting type must be APP-headed"
    );
    assert!(
        CONV_REDEX.contains(PI00),
        "its argument must be the Pi type it beta-reduces to"
    );
    assert_eq!(
        val_r11_conv_type_defeq(),
        format!("DefEq.beta {S0} {V0} {PI00}"),
        "the conversion must be one DefEq.beta, not a chain"
    );
    let gap = ty_r11_conv_gap_is_real();
    assert!(
        gap.contains(&format!("candInterp {CONV_REDEX} r5_omegaLam"))
            && gap.contains(&format!("DefEq {CONV_REDEX} {PI00}"))
            && gap.contains(&format!("candInterp {PI00} r5_omegaLam -> Empty")),
        "the gap constant must pair membership, conversion and non-membership"
    );
}

/// The conversion rule that DID land is the interpretation-equality one, and it
/// has non-`Eq.refl` content through R8's lifting equality at an arbitrary type.
#[test]
fn test_candmodel_r11_conv_rule_is_semantic_and_has_content() {
    let src = src_syn_ty_p();
    assert!(
        src.contains("Eq (KExpr -> Type) (candInterp A) (candInterp B) -> SynTyP G e B"),
        "convI must convert along INTERPRETATION equality, never along DefEq"
    );
    assert!(
        !src.contains("DefEq"),
        "the judgment must not smuggle DefEq into a rule after refuting it"
    );
    assert!(
        VAL_R11_SYNTYP_UNLIFT_TYPE.contains("candInterp_lift_eq k T d"),
        "the general content of convI is R8's lifting equality at an ARBITRARY type"
    );
    assert!(
        VAL_R11_SYNTYP_LIFT_TYPE.contains("Eq.symm (KExpr -> Type)"),
        "the lifting direction must read the same equality backwards"
    );
}

/// The declarations in REGISTRATION ORDER, driving the scratch elaboration.
fn registration_plan() -> Vec<(&'static str, String, String)> {
    let mut v: Vec<(&'static str, String, String)> =
        vec![("inductive", "SynTyP".to_string(), src_syn_ty_p())];
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
        "synTyP_fundamental",
        "synTyP_sn_subst",
        "synTyP_sn",
        "synTyP_sn_closed",
        "synTyC_to_synTyP",
        "synTyC_sn_via_synTyP",
    ] {
        v.push(get(n));
    }
    v.push((
        "def",
        "kexpr_is_const_b".to_string(),
        SRC_KEXPR_IS_CONST_B.to_string(),
    ));
    v.push((
        "def",
        "r11_pi_discr".to_string(),
        SRC_R11_PI_DISCR.to_string(),
    ));
    for n in [
        "synTyC_no_const_at_pi",
        "synTyP_id",
        "synTyP_sort_witness",
        "synTyP_konst_pi_witness",
        "synTyP_sn_konst_pi_witness",
        "synTyP_convI_witness",
        "synTyP_sn_convI_witness",
        "r11_synTyP_unlift_type",
        "r11_synTyP_lift_type",
        "synTyP_not_total",
        "r11_const_pi_rule_proper",
        "r11_conv_type_defeq",
        "r11_candInterp_top_at_app",
        "r11_conv_top_proper_incompatible",
        "r11_candInterp_conv_refuted",
        "r11_candInterp_conv_eq_refuted",
        "r11_candInterp_step_conv_refuted",
        "r11_conv_gap_is_real",
        "r11_interpEq_conv",
    ] {
        v.push(get(n));
    }
    v
}

/// The plan and the source tables name the same constants.
#[test]
fn test_candmodel_r11_plan_matches_registration() {
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
fn test_candmodel_r11_scratch_elaborates() {
    let mut spec = crate::test_utils::build_substitution_spec_with_stack();
    if spec.definitions().contains_key("SynTyP") {
        return;
    }
    let mut failures: Vec<String> = Vec::new();
    for (kind, name, src) in registration_plan() {
        let desc = "R11 scratch candidate";
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
        "R11 scratch elaboration failures ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// Registration + kernel re-verification against the substitution bundle.
#[test]
fn test_candmodel_r11_registered_and_reverifies() {
    let spec = crate::test_utils::build_substitution_spec_with_stack();
    let mut names: Vec<String> = theorem_sources().into_iter().map(|(n, _, _)| n).collect();
    for (n, _) in decl_sources() {
        names.push(n);
    }
    for name in &names {
        assert!(
            spec.definitions().contains_key(name),
            "{name} should be registered by the candmodel_construct_r11 stage"
        );
    }
    for (name, _, _) in theorem_sources() {
        spec.verify_definition(&name).unwrap_or_else(|e| {
            panic!("{name} should re-typecheck in the spec environment: {e:?}")
        });
    }
}
