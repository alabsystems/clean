// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Fail-closed pins for the `par_reduces_c_star` unique-normal-forms ladder
//! (the kernel-checked port of `proofs/lean-aristotle/unique_normal_forms.lean`,
//! port-back Item 3).
//!
//! Every ladder lemma must be a real `DerivedProved` closed term with an EMPTY
//! declared axiom closure; the statements must target EXACTLY the env-indexed
//! computational parallel reduction `par_reduces_c` / `par_reduces_c_star`
//! (never "kernel reduction" in general); and the normality predicate must be
//! the honest "reduces only to itself" notion for the REFLEXIVE
//! `par_reduces_c` (a "no step applies" normality would be degenerate).

use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec_axiom_closure::{computed_axiom_closure, foundational_rule_names};
use crate::test_utils::run_with_stack;
use crate::Specification;

/// Build the substitution subset of the spec (`add_unique_normal_forms_c` is
/// in the Substitution bundle; see `bundles.rs`). Building the spec
/// kernel-checks every registered `value_src`, so a successful build is proof
/// that all ladder proof terms type-check.
fn build_spec() -> Specification {
    run_with_stack(|| {
        Specification::new_substitution_test_spec().expect("substitution test spec should build")
    })
}

/// The ladder, bottom-up. Each entry must be DerivedProved with a value and
/// empty declared axiom_deps.
const LADDER: &[&str] = &[
    "is_normal_c",
    "normal_c_star_eq",
    "unique_normal_forms_c",
    "unique_normal_forms_c_faithful",
];

/// FAIL-CLOSED PIN: every ladder entry is a genuine DerivedProved closed term
/// (not an axiom, carries a value) with an EMPTY declared axiom closure.
#[test]
fn test_unf_c_ladder_all_derived_proved_zero_axiom_deps() {
    let spec = build_spec();
    for name in LADDER {
        let def = spec
            .definitions()
            .get(*name)
            .unwrap_or_else(|| panic!("{name} should be registered by add_unique_normal_forms_c"));
        assert!(!def.is_axiom, "{name} must not be an axiom");
        assert_eq!(
            def.category,
            AxiomCategory::DerivedLemma,
            "{name} must be a DerivedLemma"
        );
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name} must be DerivedProved (closed, kernel-checked term)"
        );
        assert!(def.value_src.is_some(), "{name} must carry a closed term");
        assert!(
            def.axiom_deps.is_empty(),
            "{name} must declare an empty axiom closure: {:?}",
            def.axiom_deps
        );
    }
}

/// STATEMENT PIN: the ladder is stated over EXACTLY `par_reduces_c` /
/// `par_reduces_c_star`, and the normality predicate is "reduces only to
/// itself" (the honest notion for the reflexive `par_reduces_c`).
#[test]
fn test_unf_c_statements_name_exact_relation() {
    let spec = build_spec();

    let isn = spec
        .definitions()
        .get("is_normal_c")
        .expect("is_normal_c should be registered");
    assert_eq!(
        isn.type_src, "RecEnv -> KExpr -> Prop",
        "is_normal_c must be an env-indexed KExpr predicate"
    );
    let isn_val = isn.value_src.as_deref().unwrap_or_default();
    assert!(
        isn_val.contains("par_reduces_c env e e' -> Eq KExpr e e'"),
        "is_normal_c must be 'every par_reduces_c reduct is e itself': {isn_val}"
    );
    assert!(
        isn.description.contains("par_reduces_c") && isn.description.contains("REFLEXIVE"),
        "is_normal_c description must name par_reduces_c and its reflexivity: {}",
        isn.description
    );

    let nse = spec
        .definitions()
        .get("normal_c_star_eq")
        .expect("normal_c_star_eq should be registered");
    assert_eq!(
        nse.type_src,
        "forall (env : RecEnv) (n : KExpr) (m : KExpr), \
         is_normal_c env n -> par_reduces_c_star env n m -> Eq KExpr n m",
        "normal_c_star_eq must be stated over par_reduces_c_star and is_normal_c"
    );

    let unf = spec
        .definitions()
        .get("unique_normal_forms_c")
        .expect("unique_normal_forms_c should be registered");
    assert_eq!(
        unf.type_src,
        "forall (env : RecEnv) (e : KExpr) (n1 : KExpr) (n2 : KExpr), \
         RecEnvReductNotRedex env -> RecEnvCtorNoRecMeta env -> \
         RecEnvClosed env -> RecEnvLiftClosed env -> \
         par_reduces_c_star env e n1 -> par_reduces_c_star env e n2 -> \
         is_normal_c env n1 -> is_normal_c env n2 -> \
         Eq KExpr n1 n2",
        "unique_normal_forms_c must join par_reduces_c_star legs under the four faithful interfaces"
    );

    let unff = spec
        .definitions()
        .get("unique_normal_forms_c_faithful")
        .expect("unique_normal_forms_c_faithful should be registered");
    assert_eq!(
        unff.type_src,
        "forall (e : KExpr) (n1 : KExpr) (n2 : KExpr), \
         par_reduces_c_star (red_rec faithful_red_env) e n1 -> \
         par_reduces_c_star (red_rec faithful_red_env) e n2 -> \
         is_normal_c (red_rec faithful_red_env) n1 -> \
         is_normal_c (red_rec faithful_red_env) n2 -> \
         Eq KExpr n1 n2",
        "the faithful corollary must be pinned to red_rec faithful_red_env"
    );
}

/// MASQUERADE GUARD: every description names the exact relation
/// (`par_reduces_c_star` / `par_reduces_c`) and never claims "unique normal
/// forms of kernel reduction" as a positive statement — the only permitted
/// mention of kernel reduction is the explicit disclaimer.
#[test]
fn test_unf_c_descriptions_name_relation_not_kernel_reduction() {
    let spec = build_spec();
    for name in LADDER {
        let def = spec.definitions().get(*name).expect("ladder entry");
        assert!(
            def.description.contains("par_reduces_c"),
            "{name} description must name the exact relation par_reduces_c: {}",
            def.description
        );
    }
    let unf = spec
        .definitions()
        .get("unique_normal_forms_c")
        .expect("unf");
    assert!(
        unf.description
            .contains("NOT \"unique normal forms of kernel reduction\""),
        "unique_normal_forms_c must carry the explicit non-kernel-reduction disclaimer: {}",
        unf.description
    );
    assert!(
        unf.description.contains("par_reduces_c_star_diamond"),
        "unique_normal_forms_c must credit the in-tree confluence discharge: {}",
        unf.description
    );
}

/// KERNEL-GROUND-TRUTH HONESTY PIN: the computed transitive axiom closure of
/// the ladder rests on the spec's FoundationalRule base only (same partition
/// as the global `spec_axiom_closure_honesty` gate, pinned locally so a
/// regression names the culprit).
#[test]
fn test_unf_c_computed_closure_is_foundational_only() {
    let spec = build_spec();
    let foundational = foundational_rule_names(&spec);
    for name in LADDER {
        let closure = computed_axiom_closure(&spec, name);
        let debt: Vec<&String> = closure.difference(&foundational).collect();
        assert!(
            debt.is_empty(),
            "{name} must have an empty non-foundational computed closure, got: {debt:?}"
        );
    }
}

/// The goal theorems re-verify against the live kernel environment (the
/// stored elaborated proof terms type-check at their declared types).
#[test]
fn test_unf_c_goals_reverify_in_kernel() {
    let spec = build_spec();
    spec.verify_definition("normal_c_star_eq")
        .expect("normal_c_star_eq should re-typecheck in the spec environment");
    spec.verify_definition("unique_normal_forms_c")
        .expect("unique_normal_forms_c should re-typecheck in the spec environment");
    spec.verify_definition("unique_normal_forms_c_faithful")
        .expect("unique_normal_forms_c_faithful should re-typecheck in the spec environment");
}
