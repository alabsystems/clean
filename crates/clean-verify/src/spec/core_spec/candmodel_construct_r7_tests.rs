// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parse-check battery for R7 of the candidate-model construction ladder.
//!
//! A `#[path]` sibling rather than an inline `mod tests`, on the convention
//! `eval_ir_kind_ord.rs` and its neighbours in this directory already use.
//! Split out when `candmodel_construct_r7.rs` crossed the 1000-line paragon
//! ratchet: the registration half and the battery that reads it back are
//! separate subjects, and the battery is the half that grows with every
//! theorem the rung gains.

use super::*;
use crate::test_utils::parse_check;

/// Every (name, type, value) triple registered via `add_definition`, in
/// registration order.
fn theorem_sources() -> Vec<(String, String, String)> {
    vec![
        (
            "betaRed_inst_transport_env".to_string(),
            TY_BETARED_INST_TRANSPORT_ENV.to_string(),
            VAL_BETARED_INST_TRANSPORT_ENV.to_string(),
        ),
        (
            "betaStar_inst_transport_env".to_string(),
            TY_BETASTAR_INST_TRANSPORT_ENV.to_string(),
            VAL_BETASTAR_INST_TRANSPORT_ENV.to_string(),
        ),
        (
            "candInterp_betaStar_closed".to_string(),
            TY_CANDINTERP_BETASTAR_CLOSED.to_string(),
            VAL_CANDINTERP_BETASTAR_CLOSED.to_string(),
        ),
        (
            "synTyT_fundamental".to_string(),
            TY_SYNTYT_FUNDAMENTAL.to_string(),
            val_syntyt_fundamental(),
        ),
        (
            "synTyT_sn_subst".to_string(),
            TY_SYNTYT_SN_SUBST.to_string(),
            VAL_SYNTYT_SN_SUBST.to_string(),
        ),
        (
            "synTyT_sn".to_string(),
            TY_SYNTYT_SN.to_string(),
            VAL_SYNTYT_SN.to_string(),
        ),
        (
            "synTyT_sn_closed".to_string(),
            TY_SYNTYT_SN_CLOSED.to_string(),
            VAL_SYNTYT_SN_CLOSED.to_string(),
        ),
        (
            "synTyT_fundamental_typesubst".to_string(),
            TY_SYNTYT_FUNDAMENTAL_TYPESUBST.to_string(),
            VAL_SYNTYT_FUNDAMENTAL_TYPESUBST.to_string(),
        ),
        (
            "r7_dev_family_derived".to_string(),
            TY_R7_DEV_FAMILY_DERIVED.to_string(),
            VAL_R7_DEV_FAMILY_DERIVED.to_string(),
        ),
        (
            "psubst_up_idsubst".to_string(),
            TY_PSUBST_UP_IDSUBST.to_string(),
            VAL_PSUBST_UP_IDSUBST.to_string(),
        ),
        (
            "synTy_to_synTyT".to_string(),
            TY_SYNTY_TO_SYNTYT.to_string(),
            val_synty_to_syntyt(),
        ),
        (
            "synTy_sn_via_synTyT".to_string(),
            TY_SYNTY_SN_VIA_SYNTYT.to_string(),
            VAL_SYNTY_SN_VIA_SYNTYT.to_string(),
        ),
        ("synTyT_id".to_string(), ty_syntyt_id(), val_syntyt_id()),
        (
            "synTyT_sort_witness".to_string(),
            ty_syntyt_sort_witness(),
            val_syntyt_sort_witness(),
        ),
        (
            "synTyT_app_witness".to_string(),
            ty_syntyt_app_witness(),
            val_syntyt_app_witness(),
        ),
        (
            "synTyT_lam_redex_witness".to_string(),
            ty_syntyt_lam_redex_witness(),
            val_syntyt_lam_redex_witness(),
        ),
        (
            "r7_redex_body_fires".to_string(),
            ty_r7_redex_body_fires(),
            val_r7_redex_body_fires(),
        ),
        (
            "r7_textbook_admits_redex_body".to_string(),
            ty_r7_textbook_admits_redex_body(),
            val_r7_textbook_admits_redex_body(),
        ),
        (
            "synTyT_sn_witness".to_string(),
            ty_syntyt_sn_witness(),
            val_syntyt_sn_witness(),
        ),
        (
            "synTyT_not_total".to_string(),
            ty_syntyt_not_total(),
            val_syntyt_not_total(),
        ),
    ]
}

/// The one inductive, as a full declaration source.
fn decl_sources() -> Vec<(String, String)> {
    vec![("SynTyT".to_string(), src_syn_ty_t())]
}

/// Parse-check every generated source — the fast guard for the commonest
/// failure class (assembly mistakes invisible to `cargo check`).
#[test]
fn test_candmodel_r7_sources_parse() {
    for (name, ty, val) in theorem_sources() {
        let assembled = format!("def {name} : {ty} := {val}");
        parse_check(&assembled)
            .unwrap_or_else(|e| panic!("{name} should parse as a def: {e}\n{assembled}"));
    }
    for (name, src) in decl_sources() {
        parse_check(&src).unwrap_or_else(|e| panic!("{name} should parse: {e}\n{src}"));
    }
}

/// PER-STRING paren balance on every source.
#[test]
fn test_candmodel_r7_sources_paren_balanced() {
    let mut all: Vec<(String, String)> = Vec::new();
    for (n, ty, val) in theorem_sources() {
        all.push((format!("{n}::ty"), ty));
        all.push((format!("{n}::val"), val));
    }
    for (n, src) in decl_sources() {
        all.push((format!("{n}::decl"), src));
    }
    for (name, src) in &all {
        let mut depth: i64 = 0;
        for ch in src.chars() {
            match ch {
                '(' => depth += 1,
                ')' => depth -= 1,
                _ => {}
            }
            assert!(depth >= 0, "close paren before its open in {name}: {src}");
        }
        assert_eq!(depth, 0, "unbalanced parens in {name}: {src}");
    }
}

/// Skip a run of parenthesised binder groups starting at `i`, returning
/// (index after the groups, how many groups were skipped).
fn skip_binder_groups(b: &[char], mut i: usize) -> (usize, usize) {
    let mut n = 0usize;
    loop {
        while i < b.len() && b[i] == ' ' {
            i += 1;
        }
        if i >= b.len() || b[i] != '(' {
            break;
        }
        let mut d = 0i64;
        while i < b.len() {
            if b[i] == '(' {
                d += 1;
            } else if b[i] == ')' {
                d -= 1;
                if d == 0 {
                    i += 1;
                    break;
                }
            }
            i += 1;
        }
        n += 1;
    }
    while i < b.len() && b[i] == ' ' {
        i += 1;
    }
    (i, n)
}

/// STRUCTURAL GUARD: a `forall` binder run must be terminated by a COMMA
/// and a `fun` binder run by `=>`.
#[test]
fn test_candmodel_r7_binder_runs_terminated() {
    let mut all: Vec<(String, String)> = Vec::new();
    for (n, ty, val) in theorem_sources() {
        all.push((format!("{n}::ty"), ty));
        all.push((format!("{n}::val"), val));
    }
    for (name, src) in &all {
        let b: Vec<char> = src.chars().collect();
        for (kw, close) in [("forall ", ","), ("fun ", "=>")] {
            let mut from = 0usize;
            while let Some(rel) = src[from..].find(kw) {
                let start = from + rel;
                from = start + 1;
                let ci = src[..start].chars().count() + kw.chars().count();
                let (after, groups) = skip_binder_groups(&b, ci);
                assert!(groups > 0, "{name}: `{kw}` with no parenthesised binder");
                let tail: String = b[after..(after + 2).min(b.len())].iter().collect();
                assert!(
                    tail.starts_with(close),
                    "{name}: `{kw}` binder run is not terminated by `{close}` — found \
                     `{tail}`"
                );
            }
        }
    }
}

/// Shape guards.
#[test]
fn test_candmodel_r7_shape_guards() {
    let syntyt = src_syn_ty_t();

    // (1) THE HEADLINE PROPERTY OF THE LADDER: the judgment is SYNTACTIC —
    // no rule may mention the interpretation, the model, or any closedness
    // premise.
    for forbidden in [
        "candInterp",
        "CandModel",
        "cm_Red",
        "RecEnvClosed",
        "RecEnvLiftClosed",
        "DefEnvClosed",
        "IsCandHF",
        "IsCandSet",
        "PiSet",
    ] {
        assert!(
            !syntyt.contains(forbidden),
            "SynTyT must not mention {forbidden} — the judgment is SYNTACTIC"
        );
    }

    // (2) THE HEADLINE PROPERTY OF R7: the lam rule is the TEXTBOOK one.
    // No development closure, therefore no betaStar and no psubst anywhere
    // in the inductive at all.
    assert!(
        syntyt.contains(LAM_RULE_TEXTBOOK),
        "SynTyT.lam must be the textbook rule `{LAM_RULE_TEXTBOOK}`"
    );
    // NB `"up "` would be a false positive — `ctx_lookup G i` contains it.
    for forbidden in ["betaStar", "psubst", "(up "] {
        assert!(
            !syntyt.contains(forbidden),
            "SynTyT must not mention {forbidden} — R7 retires R6's hoisted \
             development-closure premise, it does not respell it"
        );
    }

    // (3) The other three rules are the ordinary shapes, var going through
    // ctx_lookup.
    for needle in [
        "| var : forall (G : ListType KExpr) (i : Nat) (T : KExpr), @Eq (OptionType KExpr) \
         (ctx_lookup G i) (@OptionType.some KExpr T) -> SynTyT G (KExpr.bvar i) T",
        "| sort : forall (G : ListType KExpr) (n : Level), SynTyT G (KExpr.sort n) \
         (KExpr.sort (Level.succ n))",
        "SynTyT G f (KExpr.pi A B) -> SynTyT G a A -> SynTyT G (KExpr.app f a) B",
    ] {
        assert!(
            syntyt.contains(needle),
            "SynTyT must carry the rule `{needle}`"
        );
    }

    // (4) RECURSOR-SHAPE PIN: no fixedIndicesToParams promotion of the
    // uniform leading (G : ListType KExpr), because SynTyT.lam's recursive
    // premise concludes at the EXTENDED context.
    assert!(
        syntyt.contains("SynTyT (@ListType.cons KExpr A G) b B"),
        "SynTyT.lam's recursive premise must conclude at the EXTENDED context, or the leading \
         index becomes fixed and fixedIndicesToParams promotes it"
    );

    // (5) ARM-ARITY PIN: fields-then-IHs in constructor order, the
    // convention taken from the landed TypingCtx.rec consumer
    // fundamental_general and from R6's synTy_fundamental.
    let fund = val_syntyt_fundamental();
    assert!(
        fund.contains("(_qhf : SynTyT qG qf (KExpr.pi qA qB)) (_qha : SynTyT qG qa qA) (qihf :"),
        "the app minor must bind BOTH recursive fields before the first IH (fields-then-IHs)"
    );
    assert!(
        fund.contains(
            "(qhA : SimpleTy qA) (_qhb : SynTyT (@ListType.cons KExpr qA qG) qb qB) (qih :"
        ),
        "the lam minor must bind the SimpleTy field, then the single recursive field, then the \
         single IH"
    );
    // The lam IH is the ORDINARY one — a single body at a single
    // substitution, with no development quantifier. That is the whole rung.
    assert!(
        fund.contains(
            "(qih : forall (qs2 : Nat -> KExpr), SubstOK qs2 (ListType.cons KExpr qA qG) -> \
             candInterp qB (psubst qs2 qb))"
        ),
        "the lam IH must be the ordinary single-body one, not R6's development family"
    );

    // (6) PREMISE-FREEDOM GUARD: nothing in the capstone chain, the
    // judgment, the unlock TYPES or the bridge may carry a closedness or
    // model premise.
    for (name, ty) in [
        ("synTyT_sn", TY_SYNTYT_SN.to_string()),
        ("synTyT_sn_closed", TY_SYNTYT_SN_CLOSED.to_string()),
        ("synTyT_sn_subst", TY_SYNTYT_SN_SUBST.to_string()),
        ("synTyT_fundamental", TY_SYNTYT_FUNDAMENTAL.to_string()),
        (
            "r7_dev_family_derived",
            TY_R7_DEV_FAMILY_DERIVED.to_string(),
        ),
        ("synTy_to_synTyT", TY_SYNTY_TO_SYNTYT.to_string()),
        ("synTy_sn_via_synTyT", TY_SYNTY_SN_VIA_SYNTYT.to_string()),
        (
            "betaRed_inst_transport_env",
            TY_BETARED_INST_TRANSPORT_ENV.to_string(),
        ),
        (
            "betaStar_inst_transport_env",
            TY_BETASTAR_INST_TRANSPORT_ENV.to_string(),
        ),
        (
            "candInterp_betaStar_closed",
            TY_CANDINTERP_BETASTAR_CLOSED.to_string(),
        ),
        ("SynTyT", syntyt.clone()),
    ] {
        for forbidden in [
            "RecEnvClosed",
            "DefEnvClosed",
            "RecEnvLiftClosed",
            "CandModel",
            "cm_Red",
            "EnvAcyclic",
        ] {
            assert!(
                !ty.contains(forbidden),
                "{name} must carry no {forbidden} premise — the R7 capstone is unconditional"
            );
        }
    }
    // The capstone really is context-general, not closed-terms-only.
    assert!(
        TY_SYNTYT_SN.contains("forall (G : ListType KExpr)"),
        "synTyT_sn must hold at an ARBITRARY context (idsubst models every context)"
    );

    // (7) THE COMPLEMENTARY GUARD, and the reason R7 exists: the discharged
    // witness must actually be CONSUMED in the unlock's proof values. A
    // guard that only forbids the premise in statements would be satisfied
    // by silently re-hoisting it into the rule, which is R6.
    for (name, val) in [
        (
            "betaRed_inst_transport_env",
            VAL_BETARED_INST_TRANSPORT_ENV.to_string(),
        ),
        (
            "betaStar_inst_transport_env",
            VAL_BETASTAR_INST_TRANSPORT_ENV.to_string(),
        ),
    ] {
        assert!(
            val.contains("the_red_env_rec_closed_via_checker_b2"),
            "{name} must SUPPLY the discharged RecEnvClosed witness — that discharge is the \
             whole content of R7"
        );
    }
    // ...and the fundamental theorem must go through the unlocked form,
    // never through R2's premise-carrying one.
    assert!(
        fund.contains("betaStar_inst_transport_env") && fund.contains("candInterp_betaStar_closed"),
        "synTyT_fundamental's lam arm must build the development family from the DISCHARGED \
         transport and betaStar-closure"
    );
    assert!(
        !fund.contains("betaStar_inst_transport ") && !fund.contains("betaRed_inst_transport "),
        "synTyT_fundamental must not consume R2's premise-carrying transports directly"
    );
    // The body's SN comes from the landed fundamental_pi idiom, so no lift
    // transport is needed anywhere — RecEnvLiftClosed stays untouched.
    assert!(
        fund.contains("whnfAcc_of_instantiate_bvar0") && fund.contains("candInterp_var"),
        "the body's SN must come from the IH at the fresh variable (no lift transport)"
    );

    // (8) The fundamental theorem must consume R5's THEOREMS, never the
    // CandModel law projections of the guide's tower.
    for law in [
        "candInterp_sort_mem",
        "candInterp_app",
        "candInterp_lam",
        "candInterp_cr1",
    ] {
        assert!(
            fund.contains(law),
            "synTyT_fundamental must go through R5's landed {law}"
        );
    }
    for projection in ["red_sort", "pi_elim", "pi_intro", "redAbstraction_holds"] {
        assert!(
            !fund.contains(projection),
            "synTyT_fundamental must not consume the CandModel projection {projection}"
        );
    }

    // (9) BRIDGE-DIRECTION PIN: R7 claims SynTy -> SynTyT and nothing else.
    // The converse needs subject reduction, which is not landed.
    assert!(
        TY_SYNTY_TO_SYNTYT.contains("SynTy G e T -> SynTyT G e T"),
        "the bridge must go from R6's judgment INTO R7's"
    );
    assert!(
        !TY_SYNTY_TO_SYNTYT.contains("SynTyT G e T -> SynTy G e T"),
        "the converse bridge is not proved here and must not be claimed"
    );
    assert!(
        val_synty_to_syntyt().contains("psubst_up_idsubst"),
        "the bridge's lam arm must collapse psubst (up idsubst) b to b"
    );

    // (10) AndType SLOT PIN (the universe trap R6 measured): AndType
    // (A : Type) (B : Type) is Type-in / Type-out and the kernel is
    // NON-CUMULATIVE, so a slot may hold neither a Prop (an `Eq`) nor a
    // Type-1 term (anything quantifying over `(C : Type)`).
    let pair = ty_r7_textbook_admits_redex_body();
    assert!(
        pair.starts_with("AndType "),
        "r7_textbook_admits_redex_body should be the AndType pair"
    );
    assert!(
        !pair.contains("Eq KExpr") && !pair.contains("(C : Type)"),
        "r7_textbook_admits_redex_body: an AndType slot may hold neither a Prop `Eq` nor a \
         Type-1 `(C : Type)` quantification — split it into its own constant instead"
    );

    // (11) The witness that the textbook rule buys something must be about
    // a lam whose BODY IS A REDEX, and must be paired with the fact that
    // the body fires.
    assert!(
        ty_syntyt_lam_redex_witness().contains(LAM_REDEX),
        "the textbook-admits witness must be at lam (sort 0) (a beta redex)"
    );
    assert!(
        val_r7_textbook_admits_redex_body().contains("synTyT_lam_redex_witness")
            && val_r7_textbook_admits_redex_body().contains("r7_redex_body_fires"),
        "the pairing must consume both halves rather than restate them"
    );
    // The SN witness must go THROUGH the capstone, not around it.
    assert!(
        val_syntyt_sn_witness().starts_with("synTyT_sn "),
        "synTyT_sn_witness must be obtained by applying the capstone"
    );
}

/// Registration + kernel re-verification against the substitution bundle.
#[test]
fn test_candmodel_r7_registered_and_reverifies() {
    let spec = crate::test_utils::build_substitution_spec_with_stack();
    let mut names: Vec<String> = theorem_sources().into_iter().map(|(n, _, _)| n).collect();
    for (n, _) in decl_sources() {
        names.push(n);
    }
    for name in &names {
        assert!(
            spec.definitions().contains_key(name),
            "{name} should be registered by the candmodel_construct_r7 stage"
        );
    }
    for (name, _, _) in theorem_sources() {
        spec.verify_definition(&name).unwrap_or_else(|e| {
            panic!("{name} should re-typecheck in the spec environment: {e:?}")
        });
    }
}
