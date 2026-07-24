// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_verify::spec::{AxiomCategory, ProofStatus};
use clean_verify::test_utils::build_spec_with_stack;
use clean_verify::{DependencyAuditReport, ProofLibrary};

fn assert_spec_shape<'a>(
    spec: &'a clean_verify::Specification,
    def_name: &str,
    expected_category: AxiomCategory,
    expected_status: ProofStatus,
    expects_value_src: bool,
) -> &'a clean_verify::spec::SpecDefinition {
    let def = spec
        .definitions()
        .get(def_name)
        .unwrap_or_else(|| panic!("{def_name} should be registered"));

    assert_eq!(
        def.category, expected_category,
        "{def_name} category mismatch"
    );
    assert_eq!(
        def.proof_status, expected_status,
        "{def_name} proof_status mismatch"
    );
    assert_eq!(
        def.value_src.is_some(),
        expects_value_src,
        "{def_name} value_src presence mismatch"
    );

    def
}

fn assert_direct_axiom_deps(
    def: &clean_verify::spec::SpecDefinition,
    name: &str,
    expected_deps: &[&str],
) {
    assert_eq!(
        def.axiom_deps.len(),
        expected_deps.len(),
        "{name} should have exactly {} direct axiom deps: {:?}",
        expected_deps.len(),
        def.axiom_deps
    );
    for dep in expected_deps {
        assert!(
            def.axiom_deps.contains(*dep),
            "{name} should directly depend on {dep}: {:?}",
            def.axiom_deps
        );
    }
}

fn assert_leaf_and_constructive_frontier(spec: &clean_verify::Specification) {
    // def_eq_instantiate_arg_congr is DerivedProved: the bvar helper was
    // rerouted off def_eq_to_eq (Brick 9) and the def_eq_instantiate_arg_congr_at
    // KExpr.rec leaf carries a complete kernel-checked proof (#3221).
    let arg_congr = assert_spec_shape(
        spec,
        "def_eq_instantiate_arg_congr",
        AxiomCategory::DerivedLemma,
        ProofStatus::DerivedProved,
        true,
    );
    assert_direct_axiom_deps(
        arg_congr,
        "def_eq_instantiate_arg_congr",
        REMAINING_HELPER_AXIOMS,
    );

    assert_substitution_typing_frontier(spec);

    let type_conversion = assert_spec_shape(
        spec,
        "type_conversion",
        AxiomCategory::DerivedLemma,
        ProofStatus::DerivedProved,
        true,
    );
    assert!(
        type_conversion.axiom_deps.is_empty(),
        "type_conversion should stay fully constructive once Typing.conv is wired: {:?}",
        type_conversion.axiom_deps
    );
}

fn assert_substitution_typing_frontier(spec: &clean_verify::Specification) {
    // Brick 9 (#2859): the FALSE `def_eq_to_eq` bridge was DELETED — every consumer
    // is rerouted onto Typing.conv / sort_def_eq_eq / def_eq_respects_lift_at, so it
    // is no longer registered at all.
    assert!(
        spec.definitions().get("def_eq_to_eq").is_none(),
        "def_eq_to_eq should be deleted (Brick 9, #2859)"
    );

    // The def-eq substitution lane (#2872) is now fully constructive: the former
    // beta_subst_commutes_at same-bundle cycle is GONE — beta_subst_commutes_at
    // carries a genuine non-circular arithmetic proof (instantiate_at_app/lam +
    // DefEq.beta + instantiate_nested_commutes_zero_subst), so beta_subst_commutes,
    // beta_subst_commutes_at, def_eq_respects_subst_at, and def_eq_respects_subst
    // are DerivedProved with an empty helper-axiom closure.
    for name in [
        "beta_subst_commutes",
        "beta_subst_commutes_at",
        "def_eq_respects_subst_at",
        "def_eq_respects_subst",
    ] {
        let def = assert_spec_shape(
            spec,
            name,
            AxiomCategory::DerivedLemma,
            ProofStatus::DerivedProved,
            true,
        );
        assert!(
            def.axiom_deps.is_empty(),
            "{name} should have an empty helper-axiom closure after the #2872 cycle removal: {:?}",
            def.axiom_deps
        );
    }

    // The substitution-typing lane is now fully DerivedProved: its conv case
    // transports types via the untyped Typing.conv rule on the proved
    // def_eq_respects_subst_at (Brick 9), and the sibling
    // def_eq_instantiate_arg_congr lane graduated with the proved
    // def_eq_instantiate_arg_congr_at leaf (#3221).
    for name in ["substitution_typing_gen", "substitution_typing"] {
        let def = assert_spec_shape(
            spec,
            name,
            AxiomCategory::DerivedLemma,
            ProofStatus::DerivedProved,
            true,
        );
        assert_direct_axiom_deps(def, name, REMAINING_HELPER_AXIOMS);
    }
}

fn assert_app_case_bridge_surface(spec: &clean_verify::Specification) {
    // DerivedProved: the app cases' only formerly-pending dependency,
    // def_eq_instantiate_arg_congr, graduated with the proved
    // def_eq_instantiate_arg_congr_at leaf (#3221).
    for helper in ["app_type_preservation", "app_type_preservation_inv"] {
        let def = assert_spec_shape(
            spec,
            helper,
            AxiomCategory::DerivedLemma,
            ProofStatus::DerivedProved,
            true,
        );
        assert_direct_axiom_deps(def, helper, REMAINING_HELPER_AXIOMS);
    }

    for helper in [
        "instantiate_at_pi_codomain_eq",
        "instantiate_at_pi_self_codomain_eq",
    ] {
        let def = assert_spec_shape(
            spec,
            helper,
            AxiomCategory::DerivedLemma,
            ProofStatus::DerivedProved,
            true,
        );
        assert!(
            def.axiom_deps.is_empty(),
            "{helper} should stay fully constructive: {:?}",
            def.axiom_deps
        );
    }
}

fn assert_lam_inversion_infrastructure(spec: &clean_verify::Specification) {
    // lam_typing_dom_sort is DerivedProved (no axiom deps)
    let dom_sort = assert_spec_shape(
        spec,
        "lam_typing_dom_sort",
        AxiomCategory::DerivedLemma,
        ProofStatus::DerivedProved,
        true,
    );
    assert!(
        dom_sort.axiom_deps.is_empty(),
        "lam_typing_dom_sort should stay fully constructive: {:?}",
        dom_sort.axiom_deps
    );
}

fn assert_pi_injectivity_confluence(spec: &clean_verify::Specification) {
    // pi_injectivity_def_eq_dom/cod are DerivedProved and (after #2859) axiom-free:
    // re-pointed onto the constructive confluence tower (join_to_def_eq ∘
    // par_cd_pi_injectivity ∘ def_eq_joinable), carrying only the RedEnvFaithful
    // the_red_env hypothesis (an interface, not an axiom).
    for pi_inj in ["pi_injectivity_def_eq_dom", "pi_injectivity_def_eq_cod"] {
        let def = assert_spec_shape(
            spec,
            pi_inj,
            AxiomCategory::DerivedLemma,
            ProofStatus::DerivedProved,
            true,
        );
        assert!(
            def.axiom_deps.is_empty(),
            "{pi_inj} should be axiom-free after church_rosser_whnf retirement: {:?}",
            def.axiom_deps
        );
    }
}

fn assert_beta_preservation_surface(spec: &clean_verify::Specification) {
    assert_lam_inversion_infrastructure(spec);
    assert_pi_injectivity_confluence(spec);

    let lam_body = assert_spec_shape(
        spec,
        "lam_typing_body_subst",
        AxiomCategory::DerivedLemma,
        ProofStatus::DerivedPending,
        true,
    );
    assert_direct_axiom_deps(lam_body, "lam_typing_body_subst", &[]);
    assert!(
        !lam_body.axiom_deps.contains("def_eq_to_eq"),
        "lam_typing_body_subst should no longer directly depend on def_eq_to_eq: {:?}",
        lam_body.axiom_deps
    );
    let lam_body = spec.definitions().get("lam_typing_body_subst").unwrap();
    for resolved in [
        "delta_subst_preserves_def_eq_at",
        "iota_subst_preserves_def_eq_at",
    ] {
        assert!(
            !lam_body.axiom_deps.contains(resolved),
            "lam_typing_body_subst should no longer depend on {resolved} (#725): {:?}",
            lam_body.axiom_deps
        );
    }

    let beta_pres = assert_spec_shape(
        spec,
        "beta_preservation",
        AxiomCategory::DerivedLemma,
        ProofStatus::DerivedPending,
        true,
    );
    assert_direct_axiom_deps(beta_pres, "beta_preservation", &[]);

    let beta_exp = assert_spec_shape(
        spec,
        "beta_expansion",
        AxiomCategory::DerivedLemma,
        ProofStatus::DerivedPending,
        true,
    );
    assert_direct_axiom_deps(beta_exp, "beta_expansion", &[]);
    let beta_exp = spec.definitions().get("beta_expansion").unwrap();
    assert!(
        !beta_exp
            .axiom_deps
            .contains("typing_same_term_types_def_eq"),
        "beta_expansion should no longer list typing_same_term_types_def_eq as leaf (#461): {:?}",
        beta_exp.axiom_deps
    );

    // `typing_same_term_types_def_eq` still records the demoted bridge directly,
    // but its trust frontier collapses through `def_eq_to_eq`.
    let type_align = spec
        .definitions()
        .get("typing_same_term_types_def_eq")
        .unwrap();
    assert_direct_axiom_deps(
        type_align,
        "typing_same_term_types_def_eq",
        TYPE_PRESERVATION_DIRECT_AXIOM_DEPS,
    );
}

fn assert_pending_type_preservation_surface(spec: &clean_verify::Specification) {
    assert_def_eq_preserves_typing_surface(spec);
    assert_type_preservation_theorem_surface(spec);
}

/// Shared forbidden deps: these are resolved intermediates, NOT leaf axioms.
const FORBIDDEN_NON_LEAF_DEPS: &[&str] = &[
    "beta_preservation",
    "substitution_typing",
    "def_eq_respects_subst",
    "def_eq_typing_iff",
    "def_eq_instantiate_arg_congr",
    "beta_expansion",
    "lam_typing_body_subst",
    "typing_same_term_types_def_eq",
    "DefEq.rec_beta_typed", // eliminated by TypedDefEq lane (#2872)
    "pi_injectivity_def_eq_dom",
    "pi_injectivity_def_eq_cod", // #2851
    "delta_subst_preserves_def_eq_at",
    "iota_subst_preserves_def_eq_at", // #725
    "delta_type_preservation_fwd",
    "delta_type_preservation_bwd",
    "iota_type_preservation_fwd",
    "iota_type_preservation_bwd",
];

/// Assert a top-level theorem records only the expected HelperAxiom frontier
/// and no forbidden intermediates.
fn assert_top_level_axiom_surface(def: &clean_verify::spec::SpecDefinition, name: &str) {
    assert_direct_axiom_deps(def, name, TYPE_PRESERVATION_DIRECT_AXIOM_DEPS);
    for forbidden in FORBIDDEN_NON_LEAF_DEPS {
        assert!(
            !def.axiom_deps.contains(*forbidden),
            "{name} should not include non-leaf {forbidden}: {:?}",
            def.axiom_deps
        );
    }
}

fn assert_def_eq_preserves_typing_surface(spec: &clean_verify::Specification) {
    let def = assert_spec_shape(
        spec,
        "def_eq_preserves_typing",
        AxiomCategory::DerivedLemma,
        ProofStatus::DerivedPending,
        true,
    );
    assert_top_level_axiom_surface(def, "def_eq_preserves_typing");
}

fn assert_type_preservation_theorem_surface(spec: &clean_verify::Specification) {
    let def = assert_spec_shape(
        spec,
        "TypePreservation",
        AxiomCategory::DerivedLemma,
        ProofStatus::DerivedPending,
        true,
    );
    assert_top_level_axiom_surface(def, "TypePreservation");
    // Additional forbidden: intermediate congruence helpers flattened into TypePreservation
    for extra in [
        "app_type_preservation",
        "app_type_preservation_inv",
        "lam_type_preservation",
        "lam_type_preservation_inv",
        "pi_type_preservation",
        "pi_type_preservation_inv",
        "def_eq_preserves_typing",
    ] {
        assert!(
            !def.axiom_deps.contains(extra),
            "TypePreservation should not include intermediate {extra}: {:?}",
            def.axiom_deps
        );
    }
}

#[test]
fn test_type_preservation_spec_surface_stays_explicit() {
    let spec = build_spec_with_stack();

    assert_leaf_and_constructive_frontier(&spec);
    assert_app_case_bridge_surface(&spec);
    assert_beta_preservation_surface(&spec);
    assert_pending_type_preservation_surface(&spec);
}

fn assert_proved_audit_entry(report: &DependencyAuditReport, name: &str) {
    let entry = report
        .results
        .get(name)
        .unwrap_or_else(|| panic!("{name} should have a dependency result"));
    assert_eq!(
        entry.status,
        ProofStatus::DerivedProved,
        "{name} should be fully proved"
    );
    assert!(
        entry.axiom_deps.is_empty(),
        "{name} should not report helper-axiom dependencies: {:?}",
        entry.axiom_deps
    );
    assert!(
        entry.error.is_none(),
        "{name} should not have an audit error: {:?}",
        entry.error
    );
}

#[test]
fn test_type_preservation_proof_audit_surface_stays_narrow() {
    let spec = build_spec_with_stack();
    let lib = ProofLibrary::new();
    let report = lib.audit_dependencies(&spec);

    // After #2859 the HelperAxiom frontier is EMPTY: the audit (which counts only
    // HelperAxiom leaves) reports the whole chain as constructive. The residual
    // value-less def_eq_to_eq bridge is not a HelperAxiom and is tracked by the
    // no-new-axioms ratchet, so it does not surface here.
    for proof in [
        "TypePreservation",
        "type_preservation_helper",
        "beta_type_preservation",
        "subst_typing",
        "type_conv",
    ] {
        assert_proved_audit_entry(&report, proof);
    }
    // The intermediates that must never resurface as HelperAxiom leaves.
    for proof in ["TypePreservation", "type_preservation_helper"] {
        let result = report
            .results
            .get(proof)
            .unwrap_or_else(|| panic!("{proof} should have a dependency result"));
        for forbidden in FORBIDDEN_NON_LEAF_DEPS {
            assert!(
                !result.axiom_deps.contains(*forbidden),
                "{proof} should not include non-leaf {forbidden}: {:?}",
                result.axiom_deps
            );
        }
    }
}

/// Tracks the live trust frontier for the type preservation chain.
///
/// Authoritative current reality (after #2859):
/// - The `church_rosser_whnf` HelperAxiom is RETIRED. The chain's HelperAxiom
///   frontier is now EMPTY: every consumer is re-pointed onto the constructive
///   confluence tower (join_to_def_eq ∘ par_cd_*_injectivity ∘ def_eq_joinable,
///   carrying a `RedEnvFaithful the_red_env` hypothesis — an interface, not an
///   axiom).
/// - `def_eq_to_eq` is DELETED (Brick 9, #2859) — every consumer is rerouted
///   onto Typing.conv / sort_def_eq_eq / def_eq_respects_lift_at. The #3221
///   pillar promotion then graduated the substitution-typing lane and the app
///   congruence cases; the decls still DECLARED DerivedPending are the
///   remaining conservative pins (lam congruence cases) and the
///   beta_preservation / def_eq_typing_iff / TypePreservation lane, whose
///   HelperAxiom frontier (what `axiom_deps` records) is empty.
const REMAINING_HELPER_AXIOMS: &[&str] = &[];
const TYPE_PRESERVATION_DIRECT_AXIOM_DEPS: &[&str] = REMAINING_HELPER_AXIOMS;
// Brick 9 (#2859) DELETED the FALSE `def_eq_to_eq` bridge entirely (rerouted onto
// Typing.conv / sort_def_eq_eq / def_eq_respects_lift_at), so this list is empty.
const DERIVED_PENDING_WITHOUT_PROOFS: &[&str] = &[];

// NOTE (#2859): there is no longer a "confluence-axiom-backed" category. The
// church_rosser_whnf axiom and its pi_def_eq_eq corollary were DELETED, and
// pi_injectivity_def_eq_{dom,cod} are re-pointed onto the constructive confluence
// tower (now axiom-free), so they live in DERIVED_PROVED_CONSTRUCTIVE.

fn assert_remaining_helper_axioms(spec: &clean_verify::Specification) {
    for name in REMAINING_HELPER_AXIOMS {
        let def = spec
            .definitions()
            .get(*name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert_eq!(
            def.category,
            AxiomCategory::HelperAxiom,
            "{name} should still be a HelperAxiom"
        );
        assert!(
            def.is_axiom,
            "{name} should still be an axiom (no proof term)"
        );
    }
}

fn assert_derived_pending_without_proofs(spec: &clean_verify::Specification) {
    for name in DERIVED_PENDING_WITHOUT_PROOFS {
        let def = spec
            .definitions()
            .get(*name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert_eq!(
            def.category,
            AxiomCategory::DerivedLemma,
            "{name} should stay demoted from HelperAxiom"
        );
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedPending,
            "{name} should stay DerivedPending until its remaining bridge work lands"
        );
        assert!(!def.is_axiom, "{name} should not be tracked as an axiom");
        assert!(
            def.value_src.is_none(),
            "{name} should still lack a closed proof term"
        );
        assert_direct_axiom_deps(def, name, REMAINING_HELPER_AXIOMS);
    }
}

fn assert_derived_proved_guard(spec: &clean_verify::Specification) {
    // Fully constructive: DerivedProved with no axiom deps
    for name in [
        "type_conversion",
        "lam_typing_dom_sort",
        "pi_type_preservation",
        "pi_type_preservation_inv",
        "instantiate_at_app_preserves_def_eq",
        "instantiate_at_lam_preserves_def_eq",
        "instantiate_at_pi_preserves_def_eq",
        "def_eq_eq_left",
        "def_eq_eq_right",
        // #2872: def-eq substitution lane, same-bundle cycle removed (genuine proof)
        "beta_subst_commutes",
        "beta_subst_commutes_at",
        "def_eq_respects_subst_at",
        "def_eq_respects_subst",
        // #725: reduction witness projections (6 lemmas)
        "delta_subst_preserves_def_eq_at",
        "iota_subst_preserves_def_eq_at",
        "delta_type_preservation_fwd",
        "delta_type_preservation_bwd",
        "iota_type_preservation_fwd",
        "iota_type_preservation_bwd",
        // #461: generation lemmas for typing_same_term_types_def_eq derivation
        "typing_sort_gen",
        "typing_pi_gen",
        "typing_lam_gen",
        "typing_app_gen",
        // #2859: re-pointed onto the constructive confluence tower (axiom-free).
        "pi_injectivity_def_eq_dom",
        "pi_injectivity_def_eq_cod",
        "sort_def_eq_eq",
        // #3221: substitution-typing pillar promotion — the
        // def_eq_instantiate_arg_congr_at KExpr.rec leaf is proved, graduating
        // the wrapper, the substitution-typing lane, and the app congruence
        // cases whose sole pending reason was that leaf.
        "def_eq_instantiate_arg_congr",
        "substitution_typing_gen",
        "substitution_typing",
        "app_type_preservation",
        "app_type_preservation_inv",
        // let promotion (task #28): the context-free Typing judgment is
        // DELIBERATELY let-free, so a let_-headed term is untypeable — the
        // inversion that discharges the four beta_reduces let arms.
        "typing_let_absurd",
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name} should be DerivedProved (regression guard)"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "{name} should have no axiom deps: {:?}",
            def.axiom_deps
        );
    }
}

fn assert_derived_pending_guard(spec: &clean_verify::Specification) {
    for name in [
        // beta_subst_commutes, def_eq_respects_subst_at, and def_eq_respects_subst
        // graduated to DerivedProved in #2872 (the genuine non-circular proof of
        // beta_subst_commutes_at removed the same-bundle cycle);
        // substitution_typing_gen, substitution_typing, def_eq_instantiate_arg_congr,
        // and app_type_preservation{,_inv} graduated in #3221 (the
        // def_eq_instantiate_arg_congr_at leaf is proved); all are pinned in
        // assert_derived_proved_guard instead.
        "lam_type_preservation",
        "lam_type_preservation_inv",
        "lam_typing_body_subst",
        "beta_preservation",
        "beta_expansion",
        "def_eq_typing_iff",
        "def_eq_preserves_typing",
        "TypePreservation",
        // #461: promoted from HelperAxiom via generation lemmas + Typing.rec induction
        "typing_same_term_types_def_eq",
    ] {
        let def = spec
            .definitions()
            .get(name)
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedPending,
            "{name} should be DerivedPending (remaining conservative pending track)"
        );
        assert!(def.value_src.is_some(), "{name} should have a proof term");
        // After #2859 these decls' HelperAxiom frontier is EMPTY (church_rosser_whnf
        // retired); they stay DerivedPending only because they transitively rest on
        // the value-less def_eq_to_eq bridge, which is not a HelperAxiom and so does
        // not appear in axiom_deps. (It is tracked by the no-new-axioms ratchet.)
        assert!(
            def.axiom_deps.is_empty(),
            "{name} HelperAxiom frontier should be empty after church_rosser_whnf retirement: {:?}",
            def.axiom_deps
        );
    }
}

#[test]
fn test_type_preservation_helper_axiom_budget() {
    let spec = build_spec_with_stack();
    assert_remaining_helper_axioms(&spec);
    assert_derived_pending_without_proofs(&spec);
    assert_derived_proved_guard(&spec);
    assert_derived_pending_guard(&spec);
    assert_eq!(
        REMAINING_HELPER_AXIOMS.len(),
        0,
        "budget: 0 HelperAxiom leaves remain (church_rosser_whnf retired #2859)"
    );
}

/// Verifies that all DerivedPending proof terms were actually elaborated and
/// type-checked by the kernel (not just stored as source strings). The
/// `elaborated_value` field is set by `prepare_definition_decl` during spec
/// construction only if the proof term successfully elaborates and passes
/// `env.add_decl` type-checking.
///
/// This catches regressions where:
/// - A proof term has a syntax error (parse failure)
/// - A proof term references an undefined constant (elaboration failure)
/// - A proof term has a type mismatch (type-checking failure)
///
/// Part of #464: Phase 4A proof term integrity guard.
const DERIVED_PENDING_WITH_PROOFS: &[&str] = &[
    // beta_subst_commutes, def_eq_respects_subst_at, def_eq_respects_subst
    // graduated to DerivedProved in #2872; substitution_typing_gen,
    // substitution_typing, def_eq_instantiate_arg_congr, and
    // app_type_preservation{,_inv} graduated in #3221 (see
    // DERIVED_PROVED_CONSTRUCTIVE).
    "lam_type_preservation",
    "lam_type_preservation_inv",
    "lam_typing_body_subst",
    "beta_preservation",
    "beta_expansion",
    "def_eq_typing_iff",
    "def_eq_preserves_typing",
    "TypePreservation",
    // #461: promoted from HelperAxiom via generation lemmas + Typing.rec induction
    "typing_same_term_types_def_eq",
];

const DERIVED_PROVED_CONSTRUCTIVE: &[&str] = &[
    "type_conversion",
    "lam_typing_dom_sort",
    "pi_type_preservation",
    "pi_type_preservation_inv",
    "def_eq_app_cong",
    "def_eq_lam_cong",
    "def_eq_pi_cong",
    "instantiate_at_app_preserves_def_eq",
    "instantiate_at_lam_preserves_def_eq",
    "instantiate_at_pi_preserves_def_eq",
    // DefEq transport lemmas (promoted from DerivedPending: deps are FoundationalRules)
    "def_eq_eq_left",
    "def_eq_eq_right",
    // #2872: def-eq substitution lane, same-bundle cycle REMOVED. All four carry
    // genuine elaborated proof terms via add_definition. beta_subst_commutes_at no
    // longer routes through def_eq_respects_subst_at: it reduces the binder-depth
    // beta redex arithmetically (instantiate_at_app/lam + DefEq.beta +
    // instantiate_nested_commutes_zero_subst), so it is a value-bearing constant
    // (kernel Opaque, not a value-less axiom).
    "beta_subst_commutes",
    "beta_subst_commutes_at",
    "def_eq_respects_subst_at",
    "def_eq_respects_subst",
    // #725: reduction witness projections (6 lemmas via finite eliminable families)
    "delta_subst_preserves_def_eq_at",
    "iota_subst_preserves_def_eq_at",
    "delta_type_preservation_fwd",
    "delta_type_preservation_bwd",
    "iota_type_preservation_fwd",
    "iota_type_preservation_bwd",
    // #461: generation lemmas for typing_same_term_types_def_eq derivation
    "typing_sort_gen",
    "typing_pi_gen",
    "typing_lam_gen",
    "typing_app_gen",
    // #2859: re-pointed onto the constructive confluence tower (join_to_def_eq ∘
    // par_cd_*_injectivity ∘ def_eq_joinable). Formerly church_rosser_whnf-backed
    // DerivedProved; now axiom-free (the RedEnvFaithful the_red_env hypothesis is
    // an interface, not an axiom).
    "pi_injectivity_def_eq_dom",
    "pi_injectivity_def_eq_cod",
    "sort_def_eq_eq",
    // #3221: substitution-typing pillar promotion. The complete KExpr.rec proof
    // of def_eq_instantiate_arg_congr_at is kernel-checked at every spec build;
    // its graduation drains the sole pending reason of the wrapper, the
    // substitution-typing lane, and the app congruence cases.
    "def_eq_instantiate_arg_congr",
    "substitution_typing_gen",
    "substitution_typing",
    "app_type_preservation",
    "app_type_preservation_inv",
];

#[test]
fn test_derived_pending_proofs_elaborated() {
    let spec = build_spec_with_stack();

    for name in DERIVED_PENDING_WITH_PROOFS {
        let def = spec
            .definitions()
            .get(*name)
            .unwrap_or_else(|| panic!("{name} should be registered"));

        assert!(
            def.elaborated_type.is_some(),
            "{name}: elaborated_type should be Some (type elaboration succeeded)"
        );
        assert!(
            def.elaborated_value.is_some(),
            "{name}: elaborated_value should be Some (proof term type-checked)"
        );
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedPending,
            "{name}: should be DerivedPending"
        );
    }
}

#[test]
fn test_derived_proved_proofs_elaborated() {
    let spec = build_spec_with_stack();

    for name in DERIVED_PROVED_CONSTRUCTIVE {
        let def = spec
            .definitions()
            .get(*name)
            .unwrap_or_else(|| panic!("{name} should be registered"));

        assert!(
            def.elaborated_type.is_some(),
            "{name}: elaborated_type should be Some"
        );
        assert!(
            def.elaborated_value.is_some(),
            "{name}: elaborated_value should be Some (constructive proof elaborated)"
        );
        assert_eq!(
            def.proof_status,
            ProofStatus::DerivedProved,
            "{name}: should be DerivedProved"
        );
        assert!(
            def.axiom_deps.is_empty(),
            "{name}: should have no axiom deps (fully constructive): {:?}",
            def.axiom_deps
        );
    }
}

/// Summary test: counts all proof statuses in the type preservation chain
/// to ensure the overall progress is tracked. Any change to a lemma's status
/// (promotion or regression) will be caught.
///
/// Current budget (Part of #464, after #2851, #2856, #461, #2872, #2859, #3221):
/// - 34 DerivedProved constructive (no axiom deps) — includes beta_subst_commutes_at
///   (#2872 same-bundle cycle removed) and the #3221 substitution-typing pillar
///   promotion (def_eq_instantiate_arg_congr, substitution_typing_gen,
///   substitution_typing, app_type_preservation{,_inv})
/// - 0 DerivedProved confluence-axiom-backed (church_rosser_whnf retired)
/// - 9 DerivedPending with proof terms (empty HelperAxiom frontier; Brick 9 #2859
///   deleted the FALSE def_eq_to_eq bridge they formerly rested on)
/// - 0 DerivedPending bridge placeholders without proof term (def_eq_to_eq deleted)
/// - 0 HelperAxiom leaves (`church_rosser_whnf` retired)
#[test]
fn test_type_preservation_chain_summary() {
    let spec = build_spec_with_stack();

    assert_eq!(
        DERIVED_PROVED_CONSTRUCTIVE.len(),
        34,
        "34 constructive DerivedProved lemmas (+5 substitution-typing pillar, #3221)"
    );
    assert_eq!(
        DERIVED_PENDING_WITH_PROOFS.len(),
        9,
        "9 DerivedPending lemmas with proof terms"
    );
    assert_eq!(
        DERIVED_PENDING_WITHOUT_PROOFS.len(),
        0,
        "0 DerivedPending bridge placeholders without proof terms (def_eq_to_eq deleted #2859)"
    );
    assert_eq!(
        REMAINING_HELPER_AXIOMS.len(),
        0,
        "0 remaining HelperAxiom leaves (church_rosser_whnf retired #2859)"
    );

    // Verify all tracked lists are disjoint
    let all_names: std::collections::HashSet<&str> = DERIVED_PROVED_CONSTRUCTIVE
        .iter()
        .chain(DERIVED_PENDING_WITH_PROOFS.iter())
        .chain(DERIVED_PENDING_WITHOUT_PROOFS.iter())
        .chain(REMAINING_HELPER_AXIOMS.iter())
        .copied()
        .collect();
    assert_eq!(
        all_names.len(),
        DERIVED_PROVED_CONSTRUCTIVE.len()
            + DERIVED_PENDING_WITH_PROOFS.len()
            + DERIVED_PENDING_WITHOUT_PROOFS.len()
            + REMAINING_HELPER_AXIOMS.len(),
        "all tracked lemma names should be disjoint across the tracked categories"
    );

    // Verify all names exist in the spec
    for name in &all_names {
        assert!(
            spec.definitions().contains_key(*name),
            "{name} should be registered in the spec"
        );
    }

    // beta_subst_commutes_at is now in DERIVED_PROVED_CONSTRUCTIVE above; this
    // extra guard positively asserts the #2872 masquerade is gone — the constant
    // is value-bearing (elaborated, kernel-checked) and NOT a value-less axiom.
    assert_beta_subst_commutes_at_genuine(&spec);
}

/// Regression guard against the #2872 masquerade: `beta_subst_commutes_at` must be
/// a GENUINE value-bearing DerivedProved constant. Before the fix it was a
/// value-less kernel `Axiom` whose spec-side `proof_status`/`axiom_deps` were
/// dishonestly cleared by a "splice" while its proof routed circularly back
/// through `def_eq_respects_subst_at`. The genuine proof reduces the binder-depth
/// beta redex arithmetically (instantiate_at_app/lam + DefEq.beta +
/// instantiate_nested_commutes_zero_subst) and never touches
/// `def_eq_respects_subst_at`, so the constant elaborates to a real Opaque
/// definition (`elaborated_value` is Some) with an empty helper-axiom closure.
fn assert_beta_subst_commutes_at_genuine(spec: &clean_verify::Specification) {
    let def = spec
        .definitions()
        .get("beta_subst_commutes_at")
        .expect("beta_subst_commutes_at should be registered");
    assert_eq!(
        def.category,
        AxiomCategory::DerivedLemma,
        "beta_subst_commutes_at should be a DerivedLemma"
    );
    assert_eq!(
        def.proof_status,
        ProofStatus::DerivedProved,
        "beta_subst_commutes_at should be DerivedProved (genuine, non-circular)"
    );
    assert!(
        !def.is_axiom,
        "beta_subst_commutes_at should not be tracked as an axiom"
    );
    assert!(
        def.value_src.is_some(),
        "beta_subst_commutes_at should carry the genuine constructive proof term"
    );
    assert!(
        def.elaborated_value.is_some(),
        "beta_subst_commutes_at must be value-bearing (elaborated, kernel-checked) — \
         NOT a value-less axiom; this is the #2872 anti-masquerade guard"
    );
    assert!(
        def.axiom_deps.is_empty(),
        "beta_subst_commutes_at should have an empty helper-axiom closure: {:?}",
        def.axiom_deps
    );
}

/// Validates that manually-maintained `axiom_deps` on tracked type preservation
/// chain definitions are consistent with the transitive closure computed from
/// their `dependencies`.
///
/// For each tracked definition with an explicit `dependencies` set:
/// - Dependencies classified as HelperAxiom (leaf axioms) contribute their name
/// - Dependencies classified as DerivedLemma contribute their own axiom_deps
/// - Dependencies classified as FoundationalRule contribute nothing
///
/// The computed set must match the declared `axiom_deps`. Mismatches indicate
/// either under-reporting (false DerivedProved claims) or over-reporting
/// (stale deps from FoundationalRule refs that should have been cleared).
///
/// Part of #464: dependency tracking integrity.
#[test]
fn test_axiom_deps_transitive_consistency() {
    let spec = build_spec_with_stack();

    // Scope: all tracked definitions in the type preservation chain (including
    // beta_subst_commutes_at, now a genuine DerivedProved member of
    // DERIVED_PROVED_CONSTRUCTIVE after the #2872 cycle was removed). Each declared
    // empty axiom_deps must match the closure computed from its dependencies.
    let tracked: std::collections::HashSet<&str> = DERIVED_PROVED_CONSTRUCTIVE
        .iter()
        .chain(DERIVED_PENDING_WITH_PROOFS.iter())
        .chain(DERIVED_PENDING_WITHOUT_PROOFS.iter())
        .copied()
        .collect();

    let mut errors = Vec::new();

    for name in &tracked {
        let def = match spec.definitions().get(*name) {
            Some(d) => d,
            None => {
                errors.push(format!("{name}: not registered in spec"));
                continue;
            }
        };

        let Some(ref deps) = def.dependencies else {
            continue;
        };

        let mut computed: std::collections::HashSet<String> = std::collections::HashSet::new();
        for dep_name in deps {
            if let Some(dep_def) = spec.definitions().get(dep_name.as_str()) {
                if dep_def.category == AxiomCategory::HelperAxiom && dep_def.is_axiom {
                    // Leaf HelperAxiom: contributes its own name
                    computed.insert(dep_name.clone());
                } else {
                    // DerivedLemma or non-leaf: propagate transitive axiom_deps
                    computed.extend(dep_def.axiom_deps.iter().cloned());
                }
                // FoundationalRule with empty axiom_deps: contributes nothing
            }
            // Unresolved references (external/foundational not in spec): skip
        }

        if def.axiom_deps != computed {
            errors.push(format!(
                "{name}: declared {:?}, computed {:?}",
                def.axiom_deps, computed
            ));
        }
    }

    assert!(
        errors.is_empty(),
        "axiom_deps transitive closure mismatches in type preservation chain:\n{}",
        errors.join("\n")
    );
}
