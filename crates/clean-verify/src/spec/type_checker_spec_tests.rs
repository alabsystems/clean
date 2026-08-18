// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::collections::{BTreeSet, HashSet};

use clean_kernel::TypeChecker;

use super::TypeCheckerSpec;
use crate::spec::types::ProofStatus;
use crate::test_utils::{build_spec_with_stack, run_with_stack};

#[test]
fn test_type_checker_spec_builder_contains_expected_definitions() {
    let tc_spec = TypeCheckerSpec::new();
    let names: BTreeSet<_> = tc_spec
        .definitions()
        .iter()
        .map(|def| def.name.as_str())
        .collect();

    let expected = BTreeSet::from([
        "tc_check_completeness",
        "tc_check_type_rule",
        "tc_def_eq_transitivity",
        "tc_infer_soundness",
        "tc_infer_type_rule",
        "tc_is_def_eq_rule",
        "tc_subject_reduction",
    ]);

    assert_eq!(names, expected);
}

#[test]
fn test_type_checker_spec_definitions_exist() {
    let spec = build_spec_with_stack();

    for name in [
        "tc_check_type_rule",
        "tc_infer_type_rule",
        "tc_is_def_eq_rule",
        "tc_infer_soundness",
        "tc_check_completeness",
        "tc_def_eq_transitivity",
        "tc_subject_reduction",
    ] {
        assert!(
            spec.definitions().contains_key(name),
            "{name} should be registered"
        );
    }
}

#[test]
fn test_type_checker_spec_derived_definitions_verify() {
    let spec = build_spec_with_stack();

    for name in [
        "tc_check_type_rule",
        "tc_infer_type_rule",
        "tc_is_def_eq_rule",
        "tc_check_completeness",
        "tc_def_eq_transitivity",
        "tc_subject_reduction",
    ] {
        spec.verify_definition(name)
            .unwrap_or_else(|err| panic!("{name} should verify: {err}"));
    }
}

#[test]
fn test_tc_check_completeness_is_modulo_def_eq() {
    let spec = build_spec_with_stack();
    let def = spec
        .get_definition("tc_check_completeness")
        .expect("tc_check_completeness should exist");

    // Post-un-Skolemization: completeness concludes in the CheckDecomp existential,
    // which binds the inferred type R internally (KernelInferResult retired) with a
    // ProdType pair of the infer acceptance at R and the defeq acceptance R vs T.
    assert!(
        def.type_src.contains("CheckDecomp st e T"),
        "completeness should conclude in the CheckDecomp existential (inferred type bound \
         internally, KernelInferResult retired): {}",
        def.type_src
    );
    assert!(
        !def.type_src.contains("KernelInferResult"),
        "completeness must no longer name the retired KernelInferResult Skolem: {}",
        def.type_src
    );
    assert!(
        !def.type_src.contains("KernelInferAccepts st e T"),
        "completeness should not claim syntactic equality of the expected type: {}",
        def.type_src
    );
}

#[test]
fn test_tc_def_eq_transitivity_refl_sort_case() {
    run_with_stack(|| {
        let spec = build_spec_with_stack();
        let proof = spec
            .elaborate_source(
                "tc_def_eq_transitivity (KExpr.sort Level.zero) (KExpr.sort Level.zero) \
                 (KExpr.sort Level.zero) (DefEq.refl (KExpr.sort Level.zero)) \
                 (DefEq.refl (KExpr.sort Level.zero))",
                "tc_def_eq_transitivity refl sort case",
            )
            .expect("transitivity proof should elaborate");
        let expected = spec
            .elaborate_source(
                "is_def_eq (KExpr.sort Level.zero) (KExpr.sort Level.zero)",
                "tc_def_eq_transitivity expected type",
            )
            .expect("expected type should elaborate");

        let tc = TypeChecker::with_mode(spec.env(), spec.env().mode());
        let inferred = tc
            .infer_type(&proof)
            .expect("proof term should have an inferred type");
        assert!(
            tc.is_def_eq(&inferred, &expected),
            "expected tc_def_eq_transitivity proof to produce is_def_eq Sort0 Sort0"
        );
    });
}

#[test]
fn test_tc_subject_reduction_refl_sort_case() {
    run_with_stack(|| {
        let spec = build_spec_with_stack();
        // tc_subject_reduction is FORWARD subject reduction over the directed
        // whnf_to relation and carries a RedEnvFaithful the_red_env hypothesis
        // (#2859). We exercise its application under abstracted hypotheses
        // (hf/wd/wr and a whnf_to witness kept as binders — NEVER discharged
        // over the_red_env's concrete value): the resulting proof term must
        // type-check, confirming the threaded signature is usable.
        let proof = spec
            .elaborate_source(
                "fun (hf : RedEnvFaithful the_red_env) \
                 (wd : DefEnvWellformed the_red_env) \
                 (wr : RecEnvWellformed (red_rec the_red_env)) \
                 (hw : whnf_to (KExpr.sort Level.zero) (KExpr.sort Level.zero)) => \
                 tc_subject_reduction hf (KExpr.sort Level.zero) \
                 (KExpr.sort (Level.succ Level.zero)) (KExpr.sort Level.zero) \
                 wd wr (Typing.sort Level.zero) hw",
                "tc_subject_reduction refl sort case",
            )
            .expect("subject-reduction application should elaborate");

        let tc = TypeChecker::with_mode(spec.env(), spec.env().mode());
        let _inferred = tc
            .infer_type(&proof)
            .expect("tc_subject_reduction application should type-check");
    });
}

/// The three former termination *predicate* axioms (terminates_whnf,
/// terminates_infer, terminates_def_eq) are now faithful constructive
/// definitions via the accessibility encoding (whnf_acc / infer_acc / WHNF
/// conjunction). This guards against any regression that would reintroduce
/// them as bare `->Type` axioms or replace the bodies with a vacuous masquerade.
#[test]
fn test_termination_predicates_are_faithful_definitions() {
    let spec = build_spec_with_stack();

    for (name, body_marker) in [
        ("terminates_whnf", "whnf_acc"),
        ("terminates_infer", "infer_acc"),
        ("terminates_def_eq", "AndType"),
    ] {
        let def = spec
            .get_definition(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));

        assert!(
            !def.is_axiom,
            "{name} must not be a bare axiom — it is now a faithful definition"
        );
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name} must be DerivedProved"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "{name} must carry zero domain axiom_deps, found {:?}",
            def.axiom_deps
        );

        let value_src = def
            .value_src
            .as_ref()
            .unwrap_or_else(|| panic!("{name} must carry a constructive value_src"));
        assert!(
            value_src.contains(body_marker),
            "{name} body must reference {body_marker} (faithful accessibility \
             encoding), got: {value_src}"
        );

        // Genuine kernel re-check: the stored proof term elaborates and its
        // inferred type is def-eq to the declared type.
        spec.verify_definition(name)
            .unwrap_or_else(|err| panic!("{name} should kernel-verify: {err}"));
    }
}

/// Build a `HashSet<String>` from a list of `&str` leaf names.
fn packet_c_closure<const N: usize>(names: [&str; N]) -> HashSet<String> {
    names.into_iter().map(String::from).collect()
}

/// Assert that a single Packet C wrapper is promoted to `DerivedProved` and
/// that its `axiom_deps` matches the declared static closure.
fn assert_packet_c_wrapper(
    tc_spec: &TypeCheckerSpec,
    name: &str,
    expected_closure: &HashSet<String>,
) {
    let def = tc_spec
        .definitions()
        .iter()
        .find(|d| d.name == name)
        .unwrap_or_else(|| panic!("Packet C wrapper {name} should be registered"));

    assert!(
        !def.is_axiom,
        "Packet C wrapper {name} must not be a bare axiom"
    );
    assert!(
        def.value_src.is_some(),
        "Packet C wrapper {name} must carry a constructive value_src"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "Packet C wrapper {name} must be promoted to DerivedProved"
    );
    assert_eq!(
        &def.axiom_deps, expected_closure,
        "Packet C wrapper {name} axiom_deps must match the declared static closure"
    );
}

/// #462 Packet C regression: the four algorithmic-checker wrapper rules
/// `tc_check_type_rule`, `tc_infer_type_rule`, `tc_is_def_eq_rule`, and
/// `tc_check_completeness` must stay at `ProofStatus::DerivedProved` with
/// `axiom_deps` equal to the static closures declared at the module surface
/// (`infer_axiom_deps()` / `check_axiom_deps()` + minimal defeq leaf set).
///
/// Builder-only check (no elaborator) so it does not depend on the full
/// `build_spec_with_stack` pipeline. Locks in the Packet C promotion and
/// prevents silent demotion (e.g. a future edit that flips `proof_status`
/// back to `DerivedPending` or expands `axiom_deps` beyond the declared
/// closure).
#[test]
fn test_tc_packet_c_wrappers_are_derived_proved() {
    let tc_spec = TypeCheckerSpec::new();

    // KernelEnvValid was retired to a DerivedProved DerivedLemma (:= EnvSound), so it
    // is no longer an axiom leaf in any Packet C wrapper's transitive closure.
    // Step 3 retired the six per-case infer axioms and the opaque
    // KernelInferAccepts token (faithful inductive + kernel_infer_inversion);
    // Step 4 retired the check band too (KernelCheckAccepts is a faithful
    // inductive, kernel_check_decomposition / kernel_check_types_admissible
    // derived via KernelCheckAccepts.rec). The KernelDefEqNormalLeft/Right defeq
    // skolems were RETIRED (KernelDefEqAccepts.mk concludes in the skolem-free
    // DefEqJoinable packaged existential), so the residual on the infer/check sides
    // is the 10 infer-band skolems and the defeq side drains empty.
    // The six pi domain/codomain, lam-body-type, and level Skolems were RETIRED
    // (bound inside the App/Lam/PiInferWitness packaged existentials), so the
    // residual on the infer/check sides is now just the 3 surviving skolems.
    let infer_closure = packet_c_closure(["kernel_infer_returns_well_typed"]);
    let check_closure = infer_closure.clone();
    let defeq_closure = packet_c_closure([]);
    let completeness_closure = packet_c_closure([]);

    assert_packet_c_wrapper(&tc_spec, "tc_check_type_rule", &check_closure);
    assert_packet_c_wrapper(&tc_spec, "tc_infer_type_rule", &infer_closure);
    assert_packet_c_wrapper(&tc_spec, "tc_is_def_eq_rule", &defeq_closure);
    assert_packet_c_wrapper(&tc_spec, "tc_check_completeness", &completeness_closure);
}
