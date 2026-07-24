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
/// foundation core): the reflected `Nat.rec` (kcre_name_25; RecMeta
/// 0 params / 1 motive / 2 minors / 0 indices, major at spine position 3)
/// applied to [motive, minor_zero, minor_succ, Nat.zero (kcre_name_16)],
/// whose `iota_reduct` under `red_rec the_red_env` computes to the REAL
/// Nat.zero rule rhs applied back to the spine prefix. The current
/// `iota_reduces.mk` carries a genuine `iota_step (red_rec the_red_env) e e'`
/// witness (the graph of the computational `iota_reduct`), so tests must use
/// a redex that actually fires over the swapped env. CLOSED (no bvars), so
/// `instantiate` leaves it fixed (the zeta test relies on this).
const IOTA_REDEX: &str = concat!(
    "(KExpr.app (KExpr.app (KExpr.app (KExpr.app ",
    "(KExpr.const kcre_name_25 (ListType.nil Level)) ",
    "(KExpr.sort Level.zero)) (KExpr.sort Level.zero)) (KExpr.sort Level.zero)) ",
    "(KExpr.const kcre_name_16 (ListType.nil Level)))"
);

/// The REAL reflected Nat.zero rule rhs (fidelity-gated; see
/// `the_red_env.rs`): λ motive z s => z, level-erased.
const NAT_ZERO_RHS: &str = concat!(
    "(KExpr.lam (KExpr.pi (KExpr.const kcre_name_1 (ListType.nil Level)) (KExpr.sort kcre_nat_0)) ",
    "(KExpr.lam (KExpr.app (KExpr.bvar kcre_nat_0) (KExpr.const kcre_name_16 (ListType.nil Level))) ",
    "(KExpr.lam (KExpr.pi (KExpr.const kcre_name_1 (ListType.nil Level)) ",
    "(KExpr.pi (KExpr.app (KExpr.bvar kcre_nat_2) (KExpr.bvar kcre_nat_0)) ",
    "(KExpr.app (KExpr.bvar kcre_nat_3) (KExpr.app (KExpr.const kcre_name_10 (ListType.nil Level)) ",
    "(KExpr.bvar kcre_nat_1))))) ",
    "(KExpr.bvar kcre_nat_1))))"
);

/// The iota reduct of IOTA_REDEX: the rule rhs applied to the spine prefix
/// [motive, minor_zero, minor_succ].
fn iota_reduct() -> String {
    format!(
        "(KExpr.app (KExpr.app (KExpr.app {NAT_ZERO_RHS} \
         (KExpr.sort Level.zero)) (KExpr.sort Level.zero)) (KExpr.sort Level.zero))"
    )
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
fn beta_reduces_registers_extended_surface_constructors() {
    let spec = build_spec();
    for name in [
        "KExpr.forall_",
        "KExpr.let_",
        "beta_reduces.forall_congr_dom",
        "beta_reduces.forall_congr_cod",
        "beta_reduces.zeta",
        "beta_reduces.let_ty",
        "beta_reduces.let_val",
        "beta_reduces.let_body",
        "beta_reduces.iota",
    ] {
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
    // Let promotion (task #28): `let_` is a genuine 7th KExpr constructor and
    // zeta is a premise-free head contraction —
    //   beta_reduces (let_ ty val body) (instantiate body val).
    // Body = closed the_red_env iota redex, so `instantiate IOTA_REDEX (sort 0)`
    // computes back to the redex itself and the stated reduct is IOTA_REDEX.
    assert_definition_elaborates(
        "beta_reduces_zeta_example",
        &format!(
            "beta_reduces (KExpr.let_ (KExpr.sort Level.zero) (KExpr.sort Level.zero) {IOTA_REDEX}) \
             {IOTA_REDEX}"
        ),
        &format!("beta_reduces.zeta (KExpr.sort Level.zero) (KExpr.sort Level.zero) {IOTA_REDEX}"),
    );
}

#[test]
fn let_body_models_congruence_in_body() {
    // Let promotion (task #28): let_body is now a plain one-position congruence
    // (the OLD bundled contract-then-step reading is retired with the alias) —
    //   beta_reduces body body' -> beta_reduces (let_ ty val body) (let_ ty val body').
    // The inner step is the genuine iota firing of the closed the_red_env redex.
    let reduct = iota_reduct();
    let step_refl = iota_step_refl();
    assert_definition_elaborates(
        "beta_reduces_let_body_example",
        &format!(
            "beta_reduces (KExpr.let_ (KExpr.sort Level.zero) (KExpr.sort Level.zero) {IOTA_REDEX}) \
             (KExpr.let_ (KExpr.sort Level.zero) (KExpr.sort Level.zero) {reduct})"
        ),
        &format!(
            "beta_reduces.let_body (KExpr.sort Level.zero) (KExpr.sort Level.zero) {IOTA_REDEX} \
             {reduct} \
             (beta_reduces.iota {IOTA_REDEX} {reduct} \
             (iota_reduces.mk {IOTA_REDEX} {reduct} {step_refl}))"
        ),
    );
}

#[test]
fn iota_constructor_wraps_match_reduction_witnesses() {
    // The current iota_reduces.mk wraps a genuine computational
    // `iota_step (red_rec the_red_env)` witness: the reflected Nat.rec redex
    // fires to the real rule rhs applied to the spine prefix, by refl on
    // iota_reduct.
    let reduct = iota_reduct();
    let step_refl = iota_step_refl();
    assert_definition_elaborates(
        "beta_reduces_iota_example",
        &format!("beta_reduces {IOTA_REDEX} {reduct}"),
        &format!(
            "beta_reduces.iota {IOTA_REDEX} {reduct} \
             (iota_reduces.mk {IOTA_REDEX} {reduct} {step_refl})"
        ),
    );
}
