// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::collections::HashSet;

use clean_verify::spec::SpecDefinition;
use clean_verify::test_utils::build_spec_with_stack;
use clean_verify::{AxiomCategory, ProofStatus, ProofTerm, Specification};

fn build_spec() -> Specification {
    build_spec_with_stack()
}

fn assert_definition_elaborates(name: &str, type_src: &str, value_src: &str) {
    let mut spec = build_spec();
    spec.add_definition(SpecDefinition {
        name: name.to_string(),
        type_src: type_src.to_string(),
        value_src: None,
        is_axiom: true,
        description: "beta_reduces binder congruence regression test".to_string(),
        category: AxiomCategory::DerivedLemma,
        proof_status: ProofStatus::DerivedPending,
        elaborated_type: None,
        elaborated_value: None,
        dependencies: None,
        axiom_deps: HashSet::new(),
    })
    .unwrap_or_else(|err| panic!("{name} should register: {err:?}"));

    let proof = ProofTerm::new(name, value_src, "beta_reduces binder congruence example");
    proof
        .verify(&spec)
        .unwrap_or_else(|err| panic!("{name} should elaborate and type-check: {err:?}"));
}

#[test]
fn beta_reduces_registers_binder_congruence_constructors() {
    let spec = build_spec();
    for ctor in [
        "beta_reduces.lam_ty",
        "beta_reduces.lam_body",
        "beta_reduces.pi_dom",
        "beta_reduces.pi_cod",
    ] {
        assert!(
            spec.definitions().contains_key(ctor),
            "{ctor} should be registered in the specification"
        );
    }
}

#[test]
fn lam_ty_models_reduction_in_lambda_annotation() {
    assert_definition_elaborates(
        "beta_reduces_lam_ty_example",
        concat!(
            "beta_reduces ",
            "(KExpr.lam ",
            "(KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (KExpr.sort Level.zero)) ",
            "(KExpr.bvar Nat.zero)) ",
            "(KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero))"
        ),
        concat!(
            "beta_reduces.lam_ty ",
            "(KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (KExpr.sort Level.zero)) ",
            "(KExpr.sort Level.zero) ",
            "(KExpr.bvar Nat.zero) ",
            "(beta_reduces.beta (KExpr.sort Level.zero) (KExpr.bvar Nat.zero) (KExpr.sort Level.zero))"
        ),
    );
}

#[test]
fn lam_body_models_reduction_in_lambda_body() {
    assert_definition_elaborates(
        "beta_reduces_lam_body_example",
        concat!(
            "beta_reduces ",
            "(KExpr.lam ",
            "(KExpr.sort Level.zero) ",
            "(KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (KExpr.bvar Nat.zero))) ",
            "(KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero))"
        ),
        concat!(
            "beta_reduces.lam_body ",
            "(KExpr.sort Level.zero) ",
            "(KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (KExpr.bvar Nat.zero)) ",
            "(KExpr.bvar Nat.zero) ",
            "(beta_reduces.beta (KExpr.sort Level.zero) (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero))"
        ),
    );
}

#[test]
fn pi_dom_models_reduction_in_pi_domain() {
    assert_definition_elaborates(
        "beta_reduces_pi_dom_example",
        concat!(
            "beta_reduces ",
            "(KExpr.pi ",
            "(KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (KExpr.sort Level.zero)) ",
            "(KExpr.bvar Nat.zero)) ",
            "(KExpr.pi (KExpr.sort Level.zero) (KExpr.bvar Nat.zero))"
        ),
        concat!(
            "beta_reduces.pi_dom ",
            "(KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (KExpr.sort Level.zero)) ",
            "(KExpr.sort Level.zero) ",
            "(KExpr.bvar Nat.zero) ",
            "(beta_reduces.beta (KExpr.sort Level.zero) (KExpr.bvar Nat.zero) (KExpr.sort Level.zero))"
        ),
    );
}

#[test]
fn pi_cod_models_reduction_in_pi_codomain() {
    assert_definition_elaborates(
        "beta_reduces_pi_cod_example",
        concat!(
            "beta_reduces ",
            "(KExpr.pi ",
            "(KExpr.sort Level.zero) ",
            "(KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (KExpr.bvar Nat.zero))) ",
            "(KExpr.pi (KExpr.sort Level.zero) (KExpr.bvar Nat.zero))"
        ),
        concat!(
            "beta_reduces.pi_cod ",
            "(KExpr.sort Level.zero) ",
            "(KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (KExpr.bvar Nat.zero)) ",
            "(KExpr.bvar Nat.zero) ",
            "(beta_reduces.beta (KExpr.sort Level.zero) (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero))"
        ),
    );
}
