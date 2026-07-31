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

/// The concrete iota redex of `the_red_env` (see `the_red_env.rs`, Front #1
/// Stage 3: the_red_env := kernel_core_red_env, the reflected REAL kernel
/// foundation core): a complete closed reflected `Nat.rec`/`Nat.zero` redex
/// generated directly from the live RecMeta and selected rule, whose
/// `iota_reduct` under `red_rec the_red_env` computes to the generated reduct.
/// The current
/// `iota_reduces.mk` carries a genuine `iota_step (red_rec the_red_env) e e'`
/// witness (the graph of the computational `iota_reduct`), so tests must use
/// a redex that actually fires over the swapped env. CLOSED (no bvars), so
/// `instantiate` leaves it fixed (the zeta test relies on this). The semantic
/// endpoints are generator-owned helper definitions, so this fixture cannot
/// drift independently of recursor metadata or reflected rule structure.
fn iota_redex() -> String {
    "kcre_witness_nat_zero_redex".to_string()
}

/// The metadata-derived iota reduct paired with [`iota_redex`].
fn iota_reduct() -> String {
    "kcre_witness_nat_zero_reduct".to_string()
}

/// The `iota_step` witness for IOTA_REDEX -> its reduct: pure computation, by refl.
fn iota_step_refl() -> String {
    format!(
        "(Eq.refl (OptionType KExpr) (OptionType.some KExpr {}))",
        iota_reduct()
    )
}

fn assert_definition_elaborates(name: &str, type_src: &str, value_src: &str) {
    let mut spec = build_spec();
    spec.add_definition(SpecDefinition {
        name: name.to_string(),
        type_src: type_src.to_string(),
        value_src: None,
        is_axiom: true,
        description: "beta_reduces extended constructor regression test".to_string(),
        category: AxiomCategory::DerivedLemma,
        proof_status: ProofStatus::DerivedPending,
        elaborated_type: None,
        elaborated_value: None,
        dependencies: None,
        axiom_deps: HashSet::new(),
    })
    .unwrap_or_else(|err| panic!("{name} should register: {err:?}"));

    let proof = ProofTerm::new(name, value_src, "beta_reduces extended constructor example");
    proof
        .verify(&spec)
        .unwrap_or_else(|err| panic!("{name} should elaborate and type-check: {err:?}"));
}

#[test]
fn beta_reduces_registers_all_fifteen_constructors() {
    let spec = build_spec();
    let expected = [
        "beta_reduces.beta",
        "beta_reduces.app_left",
        "beta_reduces.app_right",
        "beta_reduces.lam_ty",
        "beta_reduces.lam_body",
        "beta_reduces.pi_dom",
        "beta_reduces.pi_cod",
        "beta_reduces.forall_congr_dom",
        "beta_reduces.forall_congr_cod",
        "beta_reduces.zeta",
        "beta_reduces.let_ty",
        "beta_reduces.let_val",
        "beta_reduces.let_body",
        "beta_reduces.iota",
        "beta_reduces.proj",
    ];
    let actual = &spec
        .env()
        .get_inductive(&clean_kernel::Name::from_string("beta_reduces"))
        .expect("beta_reduces should be registered as an inductive")
        .constructor_names;
    let expected_names = expected
        .iter()
        .map(|name| clean_kernel::Name::from_string(name))
        .collect::<Vec<_>>();
    assert_eq!(
        actual, &expected_names,
        "beta_reduces constructor set/order must be exact"
    );
    for name in expected {
        assert!(
            spec.definitions().contains_key(name),
            "{name} should be registered in the specification"
        );
    }
    for name in ["KExpr.forall_", "KExpr.let_", "KExpr.proj", "KExpr.lit"] {
        assert!(
            spec.definitions().contains_key(name),
            "{name} should be registered in the specification"
        );
    }
}

#[test]
fn forall_congr_dom_models_reduction_in_forall_domain() {
    assert_definition_elaborates(
        "beta_reduces_forall_congr_dom_example",
        concat!(
            "beta_reduces ",
            "(KExpr.forall_ ",
            "(KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (KExpr.sort Level.zero)) ",
            "(KExpr.bvar Nat.zero)) ",
            "(KExpr.forall_ (KExpr.sort Level.zero) (KExpr.bvar Nat.zero))"
        ),
        concat!(
            "beta_reduces.forall_congr_dom ",
            "(KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (KExpr.sort Level.zero)) ",
            "(KExpr.sort Level.zero) ",
            "(KExpr.bvar Nat.zero) ",
            "(beta_reduces.beta (KExpr.sort Level.zero) (KExpr.bvar Nat.zero) (KExpr.sort Level.zero))"
        ),
    );
}

#[test]
fn forall_congr_cod_models_reduction_in_forall_codomain() {
    assert_definition_elaborates(
        "beta_reduces_forall_congr_cod_example",
        concat!(
            "beta_reduces ",
            "(KExpr.forall_ ",
            "(KExpr.sort Level.zero) ",
            "(KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (KExpr.bvar Nat.zero))) ",
            "(KExpr.forall_ (KExpr.sort Level.zero) (KExpr.bvar Nat.zero))"
        ),
        concat!(
            "beta_reduces.forall_congr_cod ",
            "(KExpr.sort Level.zero) ",
            "(KExpr.app (KExpr.lam (KExpr.sort Level.zero) (KExpr.bvar Nat.zero)) (KExpr.bvar Nat.zero)) ",
            "(KExpr.bvar Nat.zero) ",
            "(beta_reduces.beta (KExpr.sort Level.zero) (KExpr.bvar Nat.zero) (KExpr.bvar Nat.zero))"
        ),
    );
}

#[test]
fn zeta_contracts_let_to_substituted_body() {
    // Let promotion (task #28): `let_` is the genuine seventh constructor in
    // the live nine-constructor KExpr model, and
    // zeta is a premise-free head contraction —
    //   beta_reduces (let_ ty val body) (instantiate body val).
    // Body = closed the_red_env iota redex, so instantiation at sort 0
    // computes back to the redex itself.
    let redex = iota_redex();
    assert_definition_elaborates(
        "beta_reduces_zeta_example",
        &format!(
            "beta_reduces (KExpr.let_ (KExpr.sort Level.zero) (KExpr.sort Level.zero) {redex}) \
             {redex}"
        ),
        &format!("beta_reduces.zeta (KExpr.sort Level.zero) (KExpr.sort Level.zero) {redex}"),
    );
}

#[test]
fn let_body_models_congruence_in_body() {
    // Let promotion (task #28): let_body is now a plain one-position congruence
    // (the OLD bundled contract-then-step reading is retired with the alias) —
    //   beta_reduces body body' -> beta_reduces (let_ ty val body) (let_ ty val body').
    // The inner step is the genuine iota firing of the closed the_red_env redex.
    let redex = iota_redex();
    let reduct = iota_reduct();
    let step_refl = iota_step_refl();
    assert_definition_elaborates(
        "beta_reduces_let_body_example",
        &format!(
            "beta_reduces (KExpr.let_ (KExpr.sort Level.zero) (KExpr.sort Level.zero) {redex}) \
             (KExpr.let_ (KExpr.sort Level.zero) (KExpr.sort Level.zero) {reduct})"
        ),
        &format!(
            "beta_reduces.let_body (KExpr.sort Level.zero) (KExpr.sort Level.zero) {redex} \
             {reduct} \
             (beta_reduces.iota {redex} {reduct} \
             (iota_reduces.mk {redex} {reduct} {step_refl}))"
        ),
    );
}

#[test]
fn iota_constructor_wraps_match_reduction_witnesses() {
    // The current iota_reduces.mk wraps a genuine computational
    // `iota_step (red_rec the_red_env)` witness: the reflected Nat.rec redex
    // fires to the real rule rhs applied to the spine prefix, by refl on
    // iota_reduct.
    let redex = iota_redex();
    let reduct = iota_reduct();
    let step_refl = iota_step_refl();
    assert_definition_elaborates(
        "beta_reduces_iota_example",
        &format!("beta_reduces {redex} {reduct}"),
        &format!(
            "beta_reduces.iota {redex} {reduct} \
             (iota_reduces.mk {redex} {reduct} {step_refl})"
        ),
    );
}
