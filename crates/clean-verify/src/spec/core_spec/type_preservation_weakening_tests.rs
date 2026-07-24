// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>

use clean_kernel::TypeChecker;

use crate::spec::types::{AxiomCategory, ProofStatus};
use crate::spec::Specification;
use crate::test_utils::{build_spec_with_stack, run_with_stack};

/// The three additive lemmas of the weakening pillar must be genuine
/// DerivedProved, kernel-checked (elaborated_value Some), non-axiom terms with an
/// empty helper-axiom closure — the HARD anti-masquerade guard for this lane.
#[test]
fn test_weakening_pillar_is_genuinely_derived_proved() {
    let spec = build_spec_with_stack();

    for name in [
        "def_eq_respects_lift_at_gen",
        "weakening_typing_gen",
        "weakening_typing",
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));

        assert_eq!(
            def.category,
            AxiomCategory::DerivedLemma,
            "{name} should be a DerivedLemma"
        );
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name} should be DerivedProved"
        );
        assert!(!def.is_axiom, "{name} must not be an axiom");
        assert!(
            def.value_src.is_some(),
            "{name} should carry a full proof term"
        );
        assert!(
            def.elaborated_value.is_some(),
            "{name} must be value-bearing (elaborated + kernel-checked), not a value-less axiom"
        );
        assert!(
            def.elaborated_type.is_some(),
            "{name} elaborated_type should be Some"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "{name} should have an empty helper-axiom closure: {:?}",
            def.axiom_deps
        );
    }
}

/// weakening_typing_gen must state the cutoff-general lift-preservation shape over
/// the reflected `has_type`/`lift_at`, and weakening_typing the cutoff-0 (`lift`)
/// specialization.
#[test]
fn test_weakening_typing_signatures() {
    let spec = build_spec_with_stack();

    let gen_def = spec
        .definitions()
        .get("weakening_typing_gen")
        .expect("weakening_typing_gen should be registered");
    assert!(
        gen_def
            .type_src
            .contains("has_type (lift_at e c amount) (lift_at T c amount)"),
        "weakening_typing_gen should conclude lift_at-preservation: {}",
        gen_def.type_src
    );
    assert!(
        gen_def.type_src.contains("has_type e T"),
        "weakening_typing_gen should take a has_type premise: {}",
        gen_def.type_src
    );

    let base = spec
        .definitions()
        .get("weakening_typing")
        .expect("weakening_typing should be registered");
    assert!(
        base.type_src
            .contains("has_type (lift e amount) (lift T amount)"),
        "weakening_typing should conclude lift-preservation at cutoff 0: {}",
        base.type_src
    );
}

/// End-to-end: a concrete application of `weakening_typing` to the closed
/// derivation `Typing.sort 0 : Typing (sort 0) (sort 1)` (under an abstracted
/// RedEnvFaithful hypothesis, NEVER discharged over the_red_env's value) must
/// elaborate AND type-check in the kernel — confirming the threaded signature is
/// usable on real typing derivations.
#[test]
fn test_weakening_typing_applies_to_concrete_sort_derivation() {
    run_with_stack(|| {
        let spec = Specification::new().expect("spec should build");
        let proof = spec
            .elaborate_source(
                "fun (hf : RedEnvFaithful the_red_env) (amount : Nat) => \
                 weakening_typing (KExpr.sort Level.zero) \
                 (KExpr.sort (Level.succ Level.zero)) amount hf (Typing.sort Level.zero)",
                "weakening_typing concrete sort application",
            )
            .expect("weakening_typing application should elaborate");

        let tc = TypeChecker::with_mode(spec.env(), spec.env().mode());
        let _inferred = tc
            .infer_type(&proof)
            .expect("weakening_typing application should type-check");
    });
}

/// End-to-end: the cutoff-general form applied at an abstract cutoff `c` to the
/// same closed derivation must also elaborate + type-check.
#[test]
fn test_weakening_typing_gen_applies_at_abstract_cutoff() {
    run_with_stack(|| {
        let spec = Specification::new().expect("spec should build");
        let proof = spec
            .elaborate_source(
                "fun (hf : RedEnvFaithful the_red_env) (amount : Nat) (c : Nat) => \
                 weakening_typing_gen (KExpr.sort Level.zero) \
                 (KExpr.sort (Level.succ Level.zero)) amount c hf (Typing.sort Level.zero)",
                "weakening_typing_gen abstract cutoff application",
            )
            .expect("weakening_typing_gen application should elaborate");

        let tc = TypeChecker::with_mode(spec.env(), spec.env().mode());
        let _inferred = tc
            .infer_type(&proof)
            .expect("weakening_typing_gen application should type-check");
    });
}
