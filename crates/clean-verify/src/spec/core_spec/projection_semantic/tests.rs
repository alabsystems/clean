// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual-registration tests; independent replay is a separate full-corpus gate.
//! Raw projection and semantic conversion callers are not typing or Rust refinement.

use super::{conversion, declarations, injectivity, join, universe, DeclarationInput};
use crate::spec::Specification;
use crate::test_utils::{run_with_stack, shared_spec};
use clean_kernel::Name;
use clean_parser::{parse_decl, SurfaceDecl};
use std::collections::HashSet;

mod checks;

struct Cohort {
    label: &'static str,
    declarations: &'static [DeclarationInput],
    proofs: &'static [&'static str],
    data: &'static [&'static str],
    carriers: &'static [&'static str],
    negatives: &'static [(&'static str, &'static str, &'static str)],
    counts: (usize, usize, usize, usize),
}

const COHORTS: &[Cohort] = &[
    Cohort {
        label: "universe",
        declarations: universe::DECLARATIONS,
        proofs: universe::PROOF_ROOTS,
        data: universe::DATA_NAMES,
        carriers: universe::INDUCTIVE_NAMES,
        negatives: universe::NEGATIVE_CONTROLS,
        counts: (15, 4, 0, 2),
    },
    Cohort {
        label: "join",
        declarations: join::DECLARATIONS,
        proofs: join::PROOF_ROOTS,
        data: join::DATA_NAMES,
        carriers: join::INDUCTIVE_NAMES,
        negatives: join::NEGATIVE_CONTROLS,
        counts: (13, 0, 1, 2),
    },
    Cohort {
        label: "conversion",
        declarations: conversion::DECLARATIONS,
        proofs: conversion::PROOF_ROOTS,
        data: conversion::DATA_NAMES,
        carriers: conversion::INDUCTIVE_NAMES,
        negatives: conversion::NEGATIVE_CONTROLS,
        counts: (21, 0, 1, 3),
    },
    Cohort {
        label: "injectivity",
        declarations: injectivity::DECLARATIONS,
        proofs: injectivity::PROOF_ROOTS,
        data: injectivity::DATA_NAMES,
        carriers: injectivity::INDUCTIVE_NAMES,
        negatives: injectivity::NEGATIVE_CONTROLS,
        counts: (26, 0, 0, 4),
    },
];

const PROP_ROOTS: &[&str] = &[
    "cdp_universe_projection_select",
    "cdp_universe_nonzero_levels",
    "par_reduces_cdp_sort_inv_eq",
    "par_reduces_cdp_star_sort_inv_eq",
    "semantic_join_cdp_sort_injective",
    "def_eq_cdp_in_sort_injective",
    "cdp_sort_nonzero_step_rigid",
    "cdp_sort_nonzero_star_rigid",
    "cdp_sort_projection_injective",
];

const RAW_ONE: &str = "(Level.succ (Level.imax (Level.param Name.anonymous) Level.zero))";
const ONE: &str = "(Level.succ Level.zero)";

fn declaration_name(declaration: &DeclarationInput) -> String {
    match declaration {
        DeclarationInput::Inductive(source) => {
            let SurfaceDecl::Inductive { name, .. } = parse_decl(source).expect("carrier AST")
            else {
                panic!("expected an inductive declaration")
            };
            checks::carrier_name(&name)
        }
        DeclarationInput::Proof(name, ..) | DeclarationInput::Data(name, ..) => (*name).to_owned(),
    }
}

#[test]
fn projection_semantic_exact_partitions_parse() {
    let mut names = HashSet::new();
    let mut ordered = Vec::new();
    let mut proof_names = Vec::new();
    for cohort in COHORTS {
        let mut proofs = Vec::new();
        let mut data = Vec::new();
        let mut carriers = Vec::new();
        for declaration in cohort.declarations {
            let name = declaration_name(declaration);
            match declaration {
                DeclarationInput::Inductive(_) => carriers.push(name.clone()),
                DeclarationInput::Proof(name, ty, body) => {
                    checks::tuple_ast(name, ty, body);
                    proofs.push(*name);
                    proof_names.push(*name);
                }
                DeclarationInput::Data(name, ty, body) => {
                    checks::tuple_ast(name, ty, body);
                    data.push(*name);
                }
            }
            assert!(names.insert(name.clone()), "duplicate {name}");
            ordered.push(name);
        }
        assert_eq!(
            (
                proofs.len(),
                data.len(),
                carriers.len(),
                cohort.negatives.len()
            ),
            cohort.counts,
            "{}: exact partition",
            cohort.label
        );
        assert_eq!(proofs, cohort.proofs, "{}: proof order", cohort.label);
        assert_eq!(data, cohort.data, "{}: transparent data", cohort.label);
        assert_eq!(carriers, cohort.carriers, "{}: real carriers", cohort.label);
    }
    assert_eq!(
        declarations().map(declaration_name).collect::<Vec<_>>(),
        ordered
    );
    assert_eq!(names.len(), 81);
    assert_eq!(proof_names.len(), 75);
    assert_eq!(PROP_ROOTS.len(), 9);
    assert_eq!(PROP_ROOTS.iter().copied().collect::<HashSet<_>>().len(), 9);
    for name in PROP_ROOTS {
        assert!(
            proof_names.contains(name),
            "Prop root must be an actual proof: {name}"
        );
    }
    let mut negatives = 0;
    for &(name, ty, body) in COHORTS.iter().flat_map(|cohort| cohort.negatives) {
        checks::tuple_ast(name, ty, body);
        assert!(
            names.insert(name.to_owned()),
            "negative name collision: {name}"
        );
        negatives += 1;
    }
    assert_eq!(negatives, 11);
    assert_eq!(names.len(), 92);
}

#[test]
fn projection_semantic_actual_records_and_carriers_recheck() {
    run_with_stack(|| {
        let spec = shared_spec();
        let (mut prop, mut type_proofs, mut data, mut carriers) = (0, 0, 0, 0);
        for declaration in declarations() {
            match declaration {
                DeclarationInput::Inductive(source) => {
                    checks::carrier(spec, source);
                    carriers += 1;
                }
                DeclarationInput::Proof(name, ty, body) => {
                    let is_prop = PROP_ROOTS.contains(name);
                    checks::record(spec, name, ty, body, Some(is_prop));
                    if is_prop {
                        prop += 1;
                    } else {
                        type_proofs += 1;
                    }
                }
                DeclarationInput::Data(name, ty, body) => {
                    checks::record(spec, name, ty, body, None);
                    data += 1;
                }
            }
        }
        assert_eq!((prop, type_proofs, data, carriers), (9, 66, 4, 2));
    });
}

fn assert_absent(spec: &Specification, name: &str) {
    assert!(!spec.definitions().contains_key(name), "{name}: no record");
    assert!(
        spec.env().get_const(&Name::from_string(name)).is_none(),
        "{name}: no kernel root"
    );
}

#[test]
fn projection_semantic_forged_evidence_is_not_registered() {
    run_with_stack(|| {
        let mut spec = shared_spec().clone();
        let mut checked = 0;
        for &(name, ty, body) in COHORTS.iter().flat_map(|cohort| cohort.negatives) {
            checks::tuple_ast(name, ty, body);
            assert_absent(&spec, name);
            let error = super::theorem(&mut spec, name, ty, body, "Actual negative proof control")
                .expect_err("well-parsed wrong proof must fail actual registration");
            assert!(
                format!("{error:?}")
                    .to_ascii_lowercase()
                    .contains("type mismatch"),
                "{name}: parsing or missing dependencies are not a negative verdict: {error:?}"
            );
            assert_absent(&spec, name);
            checked += 1;
        }
        assert_eq!(checked, 11);
    });
}

#[test]
fn projection_semantic_transparent_data_and_actual_computation() {
    run_with_stack(|| {
        let spec = shared_spec();
        checks::computes(
            spec,
            &format!("projection_post_whnf_reduct the_red_env (cdp_universe_projection {RAW_ONE})"),
            &format!("@OptionType.some KExpr (KExpr.sort {RAW_ONE})"),
        );
        checks::computes(
            spec,
            "projection_post_whnf_reduct the_red_env (instantiate_at cdp_binding_projection (KExpr.bvar (Nat.succ Nat.zero)) Nat.zero)",
            "@OptionType.some KExpr (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))))",
        );
        checks::computes(
            spec,
            &format!("cdp_universe_beta_source {ONE}"),
            &format!("KExpr.app (KExpr.lam (KExpr.sort {ONE}) (KExpr.bvar Nat.zero)) (cdp_universe_projection {ONE})"),
        );
        for (abbreviation, relation) in [
            ("CDPUniverseTransport", "par_reduces_cdp"),
            ("CDPStarUniverseTransport", "par_reduces_cdp_star"),
        ] {
            checks::computes(
                spec,
                &format!("{abbreviation} the_red_env rfnz_zero rfnz_zero KExpr"),
                &format!("forall (target : KExpr), KExprUniverseEq rfnz_zero target -> (forall (out : KExpr), {relation} the_red_env target out -> KExprUniverseEq rfnz_zero out -> KExpr) -> KExpr"),
            );
        }
        checks::not_def_eq(
            spec,
            &format!("KExpr.sort {RAW_ONE}"),
            &format!("KExpr.sort {ONE}"),
        );
        checks::not_def_eq(
            spec,
            "KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ Nat.zero)))",
            "KExpr.lam rfnz_nat (KExpr.bvar Nat.zero)",
        );
        checks::caller(
            spec,
            "cdp_universe_nonzero_levels (Level.param Name.anonymous)",
            &format!("levelEqSem {RAW_ONE} {ONE}"),
        );
    });
}

#[test]
fn projection_semantic_transport_consumes_actual_paths() {
    run_with_stack(|| {
        let spec = shared_spec();
        let target = format!("(cdp_universe_beta_source {ONE})");
        let raw_sort = format!("(KExpr.sort {RAW_ONE})");
        let result = format!("SemanticJoinCDP the_red_env {target} {raw_sort}");
        for (transport, relation, path) in [
            (
                "cdp_universe_beta_nonzero_transport",
                "par_reduces_cdp",
                format!("par_cdp_to_star the_red_env {target} out step"),
            ),
            (
                "cdp_universe_star_nonzero_transport",
                "par_reduces_cdp_star",
                "step".to_owned(),
            ),
        ] {
            let caller = format!(
                "{transport} ({result}) (fun (out : KExpr) (step : {relation} the_red_env {target} out) (related : KExprUniverseEq {raw_sort} out) => @SemanticJoinCDP.mk the_red_env {target} {raw_sort} out {raw_sort} ({path}) (@par_reduces_cdp_star.refl the_red_env {raw_sort}) (kexprUniverseEq_symm {raw_sort} out related))"
            );
            checks::caller(spec, &caller, &result);
        }
    });
}

#[test]
fn projection_semantic_connected_conversion_and_injectivity_callers() {
    run_with_stack(|| {
        let spec = shared_spec();
        let source = format!("(cdp_universe_projection {RAW_ONE})");
        let one_sort = format!("(KExpr.sort {ONE})");
        let raw_sort = format!("(KExpr.sort {RAW_ONE})");
        for name in [
            "def_eq_cdp_nonzero_projection_conversion",
            "def_eq_cdp_nonzero_projection_roundtrip",
        ] {
            checks::caller(
                spec,
                name,
                &format!("DefEqCDPIn the_red_env {source} {one_sort}"),
            );
        }
        for name in [
            "semantic_join_cdp_composed_caller",
            "def_eq_cdp_nonzero_projection_join",
        ] {
            checks::caller(
                spec,
                name,
                &format!("SemanticJoinCDP the_red_env {source} {one_sort}"),
            );
        }
        checks::caller(
            spec,
            "semantic_join_cdp_reverse_caller",
            &format!("SemanticJoinCDP the_red_env {one_sort} {source}"),
        );
        checks::caller(
            spec,
            "semantic_join_cdp_old_beta_caller",
            "SemanticJoinCDP the_red_env ctor_spine_prod_redex rfnz_zero",
        );
        checks::caller(
            spec,
            "def_eq_cdp_old_mixed_embedding",
            "DefEqCDPIn the_red_env semantic_join_mixed_source (KExpr.sort Level.zero)",
        );
        checks::caller(
            spec,
            "cdp_sort_projection_roundtrip (Level.param Name.anonymous)",
            &format!("DefEqCDPIn the_red_env {raw_sort} {one_sort}"),
        );
        checks::caller(
            spec,
            "cdp_sort_projection_injective (Level.param Name.anonymous)",
            &format!("levelEqSem {RAW_ONE} {ONE}"),
        );
        checks::caller(
            spec,
            "cdp_pi_projection_nonzero_domain (Level.param Name.anonymous)",
            &format!("DefEqCDPIn the_red_env {source} {one_sort}"),
        );
        checks::caller(
            spec,
            "cdp_pi_projection_nonzero_codomain (Level.param Name.anonymous)",
            &format!("DefEqCDPIn the_red_env (cdp_universe_beta_source {RAW_ONE}) {one_sort}"),
        );
        checks::caller(
            spec,
            &format!("cdp_pi_projection_step_domain {ONE}"),
            &format!("par_reduces_cdp the_red_env (cdp_universe_projection {ONE}) {one_sort}"),
        );
        checks::caller(spec, "def_eq_cdp_capture_projection",
            "DefEqCDPIn the_red_env (instantiate_at cdp_binding_projection (KExpr.bvar (Nat.succ Nat.zero)) Nat.zero) (KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))))");
    });
}

#[test]
fn projection_semantic_contexts_retain_new_projection_paths() {
    run_with_stack(|| {
        let spec = shared_spec();
        let source = format!("(cdp_universe_projection {RAW_ONE})");
        let raw_sort = format!("(KExpr.sort {RAW_ONE})");
        let one_sort = format!("(KExpr.sort {ONE})");
        let star = format!("(par_cdp_to_star the_red_env {source} {raw_sort} (cdp_universe_projection_step {RAW_ONE}))");
        for ctor in ["app", "lam", "pi", "forall_"] {
            checks::caller(spec,
                &format!("par_reduces_cdp_star_{ctor} the_red_env {source} {raw_sort} {source} {raw_sort} {star} {star}"),
                &format!("par_reduces_cdp_star the_red_env (KExpr.{ctor} {source} {source}) (KExpr.{ctor} {raw_sort} {raw_sort})"));
        }
        checks::caller(spec,
            &format!("par_reduces_cdp_star_let_cong the_red_env {source} {raw_sort} {source} {raw_sort} {source} {raw_sort} {star} {star} {star}"),
            &format!("par_reduces_cdp_star the_red_env (KExpr.let_ {source} {source} {source}) (KExpr.let_ {raw_sort} {raw_sort} {raw_sort})"));
        checks::caller(spec,
            &format!("par_reduces_cdp_star_proj the_red_env kcre_prod_type_name Nat.zero {source} {raw_sort} {star}"),
            &format!("par_reduces_cdp_star the_red_env (KExpr.proj kcre_prod_type_name Nat.zero {source}) (KExpr.proj kcre_prod_type_name Nat.zero {raw_sort})"));
        for ctor in ["app", "lam", "pi"] {
            checks::caller(spec,
                &format!("semantic_join_cdp_{ctor} the_red_env {source} {one_sort} {source} {one_sort} def_eq_cdp_nonzero_projection_join def_eq_cdp_nonzero_projection_join"),
                &format!("SemanticJoinCDP the_red_env (KExpr.{ctor} {source} {source}) (KExpr.{ctor} {one_sort} {one_sort})"));
        }
        checks::caller(spec,
            &format!("semantic_join_cdp_let the_red_env {source} {one_sort} {source} {one_sort} {source} {one_sort} def_eq_cdp_nonzero_projection_join def_eq_cdp_nonzero_projection_join def_eq_cdp_nonzero_projection_join"),
            &format!("SemanticJoinCDP the_red_env (KExpr.let_ {source} {source} {source}) (KExpr.let_ {one_sort} {one_sort} {one_sort})"));
        checks::caller(spec,
            &format!("semantic_join_cdp_proj the_red_env kcre_prod_type_name Nat.zero {source} {one_sort} def_eq_cdp_nonzero_projection_join"),
            &format!("SemanticJoinCDP the_red_env (KExpr.proj kcre_prod_type_name Nat.zero {source}) (KExpr.proj kcre_prod_type_name Nat.zero {one_sort})"));
        let captured =
            "(instantiate_at cdp_binding_projection (KExpr.bvar (Nat.succ Nat.zero)) Nat.zero)";
        let output = "(KExpr.lam rfnz_nat (KExpr.bvar (Nat.succ (Nat.succ Nat.zero))))";
        checks::caller(spec,
            &format!("semantic_join_cdp_lam the_red_env rfnz_nat rfnz_nat {captured} {output} (semantic_join_cdp_refl the_red_env rfnz_nat) (def_eq_cdp_in_to_semantic_join_cdp the_red_env the_red_env_faithful reflected_ctor_metadata_rigid {captured} {output} def_eq_cdp_capture_projection)"),
            &format!("SemanticJoinCDP the_red_env (KExpr.lam rfnz_nat {captured}) (KExpr.lam rfnz_nat {output})"));
    });
}

#[test]
fn projection_semantic_old_judgments_are_not_replaced() {
    run_with_stack(|| {
        let spec = shared_spec();
        checks::caller(
            spec,
            "DefEqIn.raw",
            "forall (R : RedEnv) (a b : KExpr), par_reduces_cd R a b -> DefEqIn R a b",
        );
        checks::caller(spec, "SemanticJoin.mk",
            "forall (R : RedEnv) (a b x y : KExpr), par_reduces_cd_star R a x -> par_reduces_cd_star R b y -> KExprUniverseEq x y -> SemanticJoin R a b");
        checks::caller(
            spec,
            "DefEqCDPIn.raw",
            "forall (R : RedEnv) (a b : KExpr), par_reduces_cdp R a b -> DefEqCDPIn R a b",
        );
        checks::caller(spec, "SemanticJoinCDP.mk",
            "forall (R : RedEnv) (a b x y : KExpr), par_reduces_cdp_star R a x -> par_reduces_cdp_star R b y -> KExprUniverseEq x y -> SemanticJoinCDP R a b");
    });
}
