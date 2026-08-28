// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Registration battery for R12 of the candidate-model construction ladder.
//!
//! A `#[path]` sibling rather than an inline `mod tests`, exactly as
//! `candmodel_construct_r11_tests.rs` is. Two of its tests are not guards on
//! the rung's sources but MACHINE-VISIBLE halves of the rung's two obstructions:
//! `test_candmodel_r12_value_quantified_pi_clause_is_refused` (the universe
//! horn) and `test_candmodel_r12_sval_is_not_self_referential` (the recursion
//! horn).

use super::*;
use crate::test_utils::parse_check;

/// Every source in the rung parses as a declaration — microseconds, and it
/// catches the two failure classes that cost whole elaboration cycles (a
/// parenthesised `forall` in argument position, a dropped `fun`).
#[test]
fn test_candmodel_r12_sources_parse() {
    for (name, src) in r12_all_sources() {
        parse_check(&src).unwrap_or_else(|e| panic!("{name} should parse: {e}\n{src}"));
    }
}

/// The rung's two tables name disjoint sets of constants and no name twice.
#[test]
fn test_candmodel_r12_names_are_unique() {
    let mut seen = std::collections::BTreeSet::new();
    for (name, _) in r12_all_sources() {
        assert!(seen.insert(name.clone()), "{name} is registered twice");
    }
    for required in [
        "Sk",
        "VD",
        "Val",
        "WK",
        "sval",
        "sval_good",
        "r12_sval_beta",
        "wkPiDep_elim",
        "piCandV",
        "r12_conv_contrast",
        // Every predicate the rung introduces in hypothesis position needs a
        // registered CONCLUDING definition, or the premise-satisfiability
        // ratchet (data/premise_witness_ratchet.json, which may only shrink)
        // fails. These four were the ones a constructor could not supply.
        "r12_junkEnv",
        "piCodDepIdx_var_witness",
        "wkPiDep_intro",
        "piCandV_intro",
    ] {
        assert!(
            seen.contains(required),
            "{required} must be part of the rung"
        );
    }
}

/// **THE SHAPE DOMAIN IS THE POINT.** `VD` must recurse into `Type 1` with a
/// genuine function space at `arr`, or it is not the corpus's value domain and
/// a lambda cannot denote a semantic function.
#[test]
fn test_candmodel_r12_vd_is_the_large_elimination() {
    assert!(
        SRC_VD.contains(": Type 1 :="),
        "VD must land in Type 1: the spec's candidates are KExpr -> Type, not Tm -> Prop"
    );
    assert!(
        SRC_VD.contains("(qX : Type 1) (qY : Type 1) => qX -> qY"),
        "the arr clause must be a genuine FUNCTION SPACE between value domains"
    );
    assert!(
        SRC_VD.contains("Sk.rec"),
        "VD must recurse on the SHAPE, which is the whole rung"
    );
}

/// The interpretation's two load-bearing clauses: `lam` is a semantic function
/// and `app` is semantic application. If either degrades to a term set the
/// semantic beta law stops being `Eq.refl` and R11's wall comes back.
#[test]
fn test_candmodel_r12_sval_lam_is_a_semantic_function() {
    let src = src_sval();
    assert!(
        src.contains("(qr : VEnvD qD) (qx : VD (domSk qsA)) => qihb (vconsD (domSk qsA) qD qx qr)"),
        "the lam clause must denote a SEMANTIC FUNCTION of the bound value"
    );
    assert!(
        src.contains("(qr : VEnvD qD) => qihf qr (qiha qr)"),
        "the app clause must be semantic application"
    );
    assert!(
        src.contains("WK.rec"),
        "sval must recurse on the SHAPE DERIVATION, never on the type's syntax"
    );
}

/// **THE SEMANTIC BETA LAW IS `Eq.refl`.** Not a chain, not a transport — the
/// two sides are definitionally equal, which is exactly what a term-set
/// semantics cannot arrange and what R11 measured.
#[test]
fn test_candmodel_r12_beta_law_is_definitional() {
    assert!(
        VAL_SVAL_BETA.contains("Eq.refl (VD c)"),
        "the semantic beta law must be one Eq.refl: {VAL_SVAL_BETA}"
    );
    assert!(
        VAL_SVAL_BETA_CONTRACTUM.contains("Eq.refl (VD (domSk sA))"),
        "and so must its general step-transport form"
    );
    assert!(
        val_sval_beta_transports().contains("Eq.refl"),
        "and the concrete contrast instance likewise"
    );
    // The general transport is only a conversion-invariance claim if the two
    // subjects are related by a real step. `instantiate (bvar 0) a` reduces to
    // `lift_at a 0 0`, NOT to `a`, so that link is a lemma and not `Eq.refl` —
    // measured 2026-08-27, when assuming it cost this rung an elaboration cycle.
    assert!(
        TY_BETA_STEP_GENERAL
            .contains("whnf_step (KExpr.app (KExpr.lam A (KExpr.bvar Nat.zero)) a) a"),
        "the general step must land at the argument itself: {TY_BETA_STEP_GENERAL}"
    );
    assert!(
        VAL_BETA_STEP_GENERAL.contains("r12_beta_contractum_is_arg a"),
        "and it must get there through the lift lemma, never by assuming the reduction"
    );
    assert!(
        VAL_BETA_CONTRACTUM_IS_ARG.contains("lift_zero_identity"),
        "instantiate (bvar 0) a = a is lift_zero_identity, not Eq.refl"
    );
    assert!(
        TY_SVAL_BETA_CONTRACTUM.contains("(sval D a (domSk sA) ha r)"),
        "the transport's right-hand side must be the interpretation of the STEP TARGET"
    );
}

/// **THE R11 CONTRAST IS REGISTERED**, at R11's own refutation and at a genuine
/// type-level beta redex whose head former is `app` and whose contractum's is
/// not.
#[test]
fn test_candmodel_r12_conv_contrast_pairs_r11() {
    assert!(
        val_conv_contrast().contains("r11_candInterp_step_conv_refuted"),
        "the contrast must carry R11's refutation itself, not a restatement"
    );
    assert!(
        TY_CONV_CONTRAST.contains("r12_candInterpStepConv -> Empty")
            && TY_CONV_CONTRAST.contains("r12_svalTransportsBeta"),
        "the contrast must pair the refuted transport with the proved one: {TY_CONV_CONTRAST}"
    );
    assert!(
        SRC_CANDINTERP_STEP_CONV
            .contains("whnf_step qA qB -> candInterp qA qe -> candInterp qB qe"),
        "the refuted half must be stated at ONE whnf_step of the TYPE, R11's sharpest form"
    );
    assert!(
        SRC_BETA_REDEX.contains("KExpr.app (KExpr.lam"),
        "the transported redex must be APP-headed, like R11's"
    );
    assert!(
        val_beta_step_witness().contains("whnf_step.beta"),
        "and it must genuinely take the step R11 refuted transport for"
    );
}

/// **HORN 2, PINNED: the recursion horn.** `sval` may not mention itself — its
/// `pi` clause is the junk probe — while the dependent candidate is built on top
/// of `sval` and does mention it. That stratification is not a style choice: the
/// derivation-indexed intersection calls `sval` at derivations of terms
/// unrelated to the one being interpreted, so it cannot be a minor of `sval`'s
/// own `WK.rec`.
#[test]
fn test_candmodel_r12_sval_is_not_self_referential() {
    let src = src_sval();
    let body = match src.split_once(":=") {
        Some((_, b)) => b,
        None => panic!("sval must be a def with a body"),
    };
    assert!(
        !body.contains("sval"),
        "sval's own body must not call sval: the pi clause is the junk probe, by construction"
    );
    assert!(
        SRC_PI_COD_DEP_IDX.contains("sval D qy d qhy r"),
        "the dependent codomain must call sval at an UNRELATED derivation — that is the horn"
    );
    assert!(
        SRC_WK_PI_DEP.contains("piCandDep"),
        "wkPiDep must be built on top of piCandDep, after sval, never inside it"
    );
}

/// **HORN 1, PINNED: the universe horn.** The value-quantified clause is
/// registered at `KExpr -> Type 1`, one universe above the `KExpr -> Type` that
/// `VD Sk.ty` is.
#[test]
fn test_candmodel_r12_value_quantified_clause_is_one_universe_up() {
    assert!(
        SRC_PI_CAND_V.contains(": KExpr -> Type 1 :="),
        "piCandV must be registered at its TRUE universe: {SRC_PI_CAND_V}"
    );
    assert!(
        SRC_PI_CAND_V.contains("forall (qv : VD d), GoodD d qv ->"),
        "and it must be the corpus's clause: an intersection over the whole value domain"
    );
    assert!(
        SRC_PI_COD_DEP_IDX.contains(": Type :="),
        "the derivation-indexed replacement must be at Type 0, or it buys nothing"
    );
}

/// The dependent elimination reads the codomain AT THE ARGUMENT'S OWN VALUE.
/// If it ever reads it at the junk value it is R6's non-dependent `app` rule
/// again and the rung's deliverable C is gone.
#[test]
fn test_candmodel_r12_dependent_elim_is_dependent() {
    assert!(
        TY_WKPIDEP_ELIM.contains("vconsD (domSk sA) D (sval D a (domSk sA) ha r) r"),
        "the eliminated codomain must be interpreted under the ARGUMENT'S value: {TY_WKPIDEP_ELIM}"
    );
    assert!(
        TY_WKPIDEP_ELIM.contains("forall (ha : WK D a (domSk sA))"),
        "the argument's SHAPE DERIVATION is what supplies that value"
    );
    assert!(
        TY_PICANDDEP_ELIM.contains("vcarD sB (GB (sval D a d ha r)) (KExpr.app t a)"),
        "and the underlying candidate's elimination likewise"
    );
}

/// The rung carries no `CandModel`, and never claims to.
#[test]
fn test_candmodel_r12_carries_no_candmodel_premise() {
    for (name, src) in r12_all_sources() {
        for banned in [
            "CandModel",
            "RecEnvClosed",
            "RecEnvLiftClosed",
            "DefEnvClosed",
            "EnvAcyclic",
        ] {
            assert!(
                !src.contains(banned),
                "{name} must not carry {banned}: R12 proves nothing about M"
            );
        }
    }
}

/// SCRATCH ELABORATION — the iteration tool for this rung.
#[test]
fn test_candmodel_r12_scratch_elaborates() {
    let mut spec = crate::test_utils::build_substitution_spec_with_stack();
    if spec.definitions().contains_key("sval") {
        return;
    }
    let mut failures: Vec<String> = Vec::new();
    for (kind, name, src) in r12_decl_sources() {
        let result = match kind {
            "inductive" => spec.add_inductive(&src, "R12 scratch candidate"),
            _ => spec.add_recursive_def(&src, "R12 scratch candidate"),
        };
        if let Err(e) = result {
            failures.push(format!("{name}: {e}"));
        }
    }
    for (name, ty, val) in r12_theorem_sources() {
        let src = format!("def {name} : {ty} := {val}");
        if let Err(e) = spec.add_recursive_def(&src, "R12 scratch candidate") {
            failures.push(format!("{name}: {e}"));
        }
    }
    assert!(
        failures.is_empty(),
        "R12 scratch elaboration failures ({}):\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// **HORN 1, MACHINE-VISIBLE.** The corpus's value-quantified Pi clause written
/// at the universe the candidate interface demands is REFUSED by the kernel.
/// This is the rung's first obstruction as a measurement rather than a claim: a
/// `-> Empty` theorem cannot state a universe fact, but a refused declaration
/// can.
#[test]
fn test_candmodel_r12_value_quantified_pi_clause_is_refused() {
    let mut spec = crate::test_utils::build_substitution_spec_with_stack();
    let at_type0 = SRC_PI_CAND_V
        .replace("def piCandV ", "def r12_piCandV_probe ")
        .replace(": KExpr -> Type 1 :=", ": KExpr -> Type :=");
    assert!(
        at_type0.contains(": KExpr -> Type :="),
        "the probe must ask for the clause at the CANDIDATE universe"
    );
    let result = spec.add_recursive_def(&at_type0, "R12 universe-horn probe (must fail)");
    assert!(
        result.is_err(),
        "the value-quantified Pi clause must NOT typecheck at KExpr -> Type: Type is predicative \
         and VD d : Type 1, so the corpus's clause lands one universe up. If this ever passes, \
         R12's first obstruction is wrong and the whole dependent Pi clause can move into sval."
    );
}

/// **THE PREMISE-SATISFIABILITY CHECK, DRIFT-PROOF.** Not one predicate this
/// rung introduces may be ASSUMED somewhere and CONCLUDED by nothing. The name
/// set is derived from the rung's own source tables rather than hand-written, so
/// a constant added later cannot slip past it — the hand-written list in
/// `premise_witness::tests::test_candmodel_ladder_premises_are_witnessed` is the
/// standing-rule record, this is the guard.
///
/// This is also the substitution-bundle stand-in for the full-spec ratchet
/// (`tests/premise_witness_gate.rs`), which measured 28.8 GB peak RSS at
/// declared weight 44 and therefore CANNOT run on a 16 GB machine. R12 lives in
/// the substitution bundle, so every R12 name it would check is checked here;
/// what it additionally covers are stages R12 does not touch.
#[test]
fn test_candmodel_r12_introduces_no_unwitnessed_premise() {
    let spec = crate::test_utils::build_substitution_spec_with_stack();
    let mine: std::collections::BTreeSet<String> =
        r12_all_sources().into_iter().map(|(n, _)| n).collect();
    let live: Vec<String> = crate::premise_witness::unwitnessed_premises(&spec)
        .into_iter()
        .map(|u| u.predicate)
        .filter(|p| mine.contains(p))
        .collect();
    assert!(
        live.is_empty(),
        "R12 introduces {} predicate(s) that are ASSUMED in the spec and CONCLUDED by nothing the \
         gate can see: {}. A conditional theorem whose premises cannot be satisfied is a \
         NON-result that passes the axiom census while looking green. Register a definition whose \
         stored type keeps the predicate as its syntactic HEAD — a constructor does not count.",
        live.len(),
        live.join(", ")
    );
}

/// Registration + kernel re-verification against the substitution bundle.
#[test]
fn test_candmodel_r12_registered_and_reverifies() {
    let spec = crate::test_utils::build_substitution_spec_with_stack();
    for (name, _) in r12_all_sources() {
        assert!(
            spec.definitions().contains_key(&name),
            "{name} should be registered by the candmodel_construct_r12 stage"
        );
    }
    for (name, _, _) in r12_theorem_sources() {
        spec.verify_definition(&name).unwrap_or_else(|e| {
            panic!("{name} should re-typecheck in the spec environment: {e:?}")
        });
    }
}
