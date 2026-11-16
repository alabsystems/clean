// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! In-crate unit tests for the honesty shell.

use crate::badge::{compute_badge, Label, ProofFloor, TrustedModels};
use crate::divergence::{DivergenceClosure, RefinementDivergenceKind, TaggedRefinement};
use crate::enforcement::{
    evidence_satisfies, runtime_never_satisfies_certified, runtime_observed_strength,
};
use crate::inference_meter::InferenceMeter;
use crate::phase::Phase;
use clean_cake::goodness::{FloorLevel, Goodness};
use trust_ir_contract::translation_validation::{CheckKind, RefinementVc, TranslationCheck};
use trust_ir_contract::{BlockId, Formula, TrustSpecVariableOrigin};

/// A clean, foundational proof-depth meter: empty axioms/markers.
fn foundational_goodness() -> Goodness {
    Goodness {
        g_mass: 10.0,
        floor: FloorLevel::Foundational,
        closure_size: 8,
        domain_axioms: Vec::new(),
        trust_markers: Vec::new(),
    }
}

fn the_three_models() -> TrustedModels {
    TrustedModels::all_three()
}

fn empty_inference() -> InferenceMeter {
    InferenceMeter::new()
}

/// An inference meter with one recorded inferred binding (NON-empty).
fn nonempty_inference() -> InferenceMeter {
    let mut m = InferenceMeter::new();
    m.record_inferred(&TrustSpecVariableOrigin::Inferred);
    m
}

fn sample_vc() -> RefinementVc {
    RefinementVc {
        check: TranslationCheck {
            source_point: BlockId(0),
            target_point: BlockId(0),
            kind: CheckKind::ReturnValue,
            formula: Formula::Bool(true),
            description: "sample refinement".to_string(),
        },
        source_function: "src".to_string(),
        target_function: "tgt".to_string(),
    }
}

fn improvement() -> TaggedRefinement {
    TaggedRefinement::new(sample_vc(), RefinementDivergenceKind::Improvement)
}

fn externally_coupled() -> TaggedRefinement {
    TaggedRefinement::new(sample_vc(), RefinementDivergenceKind::ExternallyCoupled)
}

fn latent_bug() -> TaggedRefinement {
    TaggedRefinement::new(
        sample_vc(),
        RefinementDivergenceKind::LatentBugExposed {
            counterexample: "x = i32::MIN".to_string(),
        },
    )
}

#[test]
fn test_badge_phase_runtime_instance_denies_certified() {
    // Foundational floor, empty axioms/markers, clean-core divergence, all three
    // models — but RuntimeInstance phase. The PHASE gate must deny.
    let g = foundational_goodness();
    let report = compute_badge(
        Some(&g),
        Phase::RuntimeInstance,
        &the_three_models(),
        &empty_inference(),
        &DivergenceClosure::new(),
    );
    assert_ne!(
        report.label,
        Label::RustCertifiedToBinary,
        "RuntimeInstance phase must deny RustCertifiedToBinary"
    );
}

#[test]
fn test_badge_goodness_none_fails_closed() {
    let report = compute_badge(
        None,
        Phase::StaticUniversal,
        &the_three_models(),
        &empty_inference(),
        &DivergenceClosure::new(),
    );
    assert_ne!(
        report.label,
        Label::RustCertifiedToBinary,
        "goodness=None must fail closed, never certified"
    );
    assert!(
        report.proof_depth.is_none(),
        "no proof-depth meter when goodness=None"
    );
}

#[test]
fn test_badge_non_foundational_floor_denies() {
    let mut g = foundational_goodness();
    g.floor = FloorLevel::AxiomDependent;
    let report = compute_badge(
        Some(&g),
        Phase::StaticUniversal,
        &the_three_models(),
        &empty_inference(),
        &DivergenceClosure::new(),
    );
    assert_ne!(report.label, Label::RustCertifiedToBinary);
}

#[test]
fn test_badge_domain_axioms_present_denies() {
    let mut g = foundational_goodness();
    g.domain_axioms = vec!["my.domain.axiom".to_string()];
    let report = compute_badge(
        Some(&g),
        Phase::StaticUniversal,
        &the_three_models(),
        &empty_inference(),
        &DivergenceClosure::new(),
    );
    assert_ne!(report.label, Label::RustCertifiedToBinary);
}

#[test]
fn test_badge_trust_markers_present_denies() {
    let mut g = foundational_goodness();
    g.trust_markers = vec!["sorryAx".to_string()];
    let report = compute_badge(
        Some(&g),
        Phase::StaticUniversal,
        &the_three_models(),
        &empty_inference(),
        &DivergenceClosure::new(),
    );
    assert_ne!(report.label, Label::RustCertifiedToBinary);
}

#[test]
fn test_badge_externally_coupled_divergence_denies() {
    let g = foundational_goodness();
    let divergence = DivergenceClosure::from_vec(vec![externally_coupled()]);
    let report = compute_badge(
        Some(&g),
        Phase::StaticUniversal,
        &the_three_models(),
        &empty_inference(),
        &divergence,
    );
    assert_ne!(report.label, Label::RustCertifiedToBinary);
}

#[test]
fn test_badge_extra_model_beyond_three_denies() {
    // Missing one of the three named models => not the exact trusted base.
    let g = foundational_goodness();
    let models = TrustedModels {
        isa: true,
        runtime: true,
        semantic_reflection: false,
    };
    let report = compute_badge(
        Some(&g),
        Phase::StaticUniversal,
        &models,
        &empty_inference(),
        &DivergenceClosure::new(),
    );
    assert_ne!(report.label, Label::RustCertifiedToBinary);
}

#[test]
fn test_badge_grants_certified_with_nonempty_inference_meter() {
    // SECTION-6 CORRECTION: a NON-EMPTY inference meter must NOT deny
    // RustCertifiedToBinary. Everything else satisfies the gate.
    let g = foundational_goodness();
    let inference = nonempty_inference();
    assert!(
        !inference.is_empty(),
        "precondition: inference meter is non-empty"
    );

    let report = compute_badge(
        Some(&g),
        Phase::StaticUniversal,
        &the_three_models(),
        &inference,
        &DivergenceClosure::new(),
    );
    assert_eq!(
        report.label,
        Label::RustCertifiedToBinary,
        "non-empty inference meter must NOT be a gate (cardinal-error rule)"
    );
    // And the meter is still disclosed side by side.
    assert_eq!(report.inference.inferred_count, 1);
    assert!(report.inference.faithfulness_obligation_open);
}

#[test]
fn test_badge_grants_certified_clean_core_improvement_only() {
    // Clean-core (improvement-only) divergence still grants the badge.
    let g = foundational_goodness();
    let divergence = DivergenceClosure::from_vec(vec![improvement()]);
    let report = compute_badge(
        Some(&g),
        Phase::StaticUniversal,
        &the_three_models(),
        &empty_inference(),
        &divergence,
    );
    assert_eq!(report.label, Label::RustCertifiedToBinary);
}

#[test]
fn test_runtime_observed_never_satisfies_certified() {
    assert!(
        runtime_never_satisfies_certified(),
        "RuntimeObserved must never satisfy a Certified requirement (rail 6)"
    );
}

#[test]
fn test_divergence_improvement_only_is_clean_core() {
    let mut d = DivergenceClosure::from_vec(vec![improvement(), improvement()]);
    assert!(d.is_clean_core(), "improvement-only closure is clean-core");
    assert!(!d.has_externally_coupled());

    d.push(externally_coupled());
    assert!(
        !d.is_clean_core(),
        "adding ExternallyCoupled breaks clean-core"
    );
    assert!(d.has_externally_coupled());
}

#[test]
fn test_empty_divergence_is_clean_core() {
    let d = DivergenceClosure::new();
    assert!(d.is_clean_core());
    assert!(d.is_empty());
}

#[test]
fn test_inference_meter_local_origin_does_not_increment() {
    let mut m = InferenceMeter::new();
    m.record_inferred(&TrustSpecVariableOrigin::Local { index: 0 });
    m.record_inferred(&TrustSpecVariableOrigin::Quantified);
    assert!(m.is_empty(), "only Inferred origins increment the meter");
    assert!(!m.faithfulness_obligation_open());
}

// ---------------------------------------------------------------------------
// §5b FLAW rail: a witnessed LatentBugExposed FORBIDS every certified/proven
// label. These tests pin the bug that previously let a FLAW earn
// CertifiedToSpecModuloInferred.
// ---------------------------------------------------------------------------

#[test]
fn test_badge_latent_bug_denies_all_certified_labels_returns_flaw_witnessed() {
    // The proof-depth meter is foundational and (apart from the FLAW) everything
    // else would qualify for a certified-flavored label. The witnessed
    // counterexample must override ALL of them and yield FlawWitnessed.
    let g = foundational_goodness();
    let divergence = DivergenceClosure::from_vec(vec![latent_bug()]);
    assert_eq!(divergence.latent_bug_count(), 1);
    assert!(divergence.has_latent_bug());

    // StaticUniversal + all three models would normally certify-to-binary.
    let report = compute_badge(
        Some(&g),
        Phase::StaticUniversal,
        &the_three_models(),
        &empty_inference(),
        &divergence,
    );
    assert_eq!(
        report.label,
        Label::FlawWitnessed { counterexamples: 1 },
        "a witnessed FLAW must yield FlawWitnessed, never a certified label"
    );

    // RuntimeInstance phase (where it would otherwise be CertifiedToSpec...) —
    // still FlawWitnessed, never any certified/SMT label.
    let report_rt = compute_badge(
        Some(&g),
        Phase::RuntimeInstance,
        &the_three_models(),
        &empty_inference(),
        &divergence,
    );
    assert_eq!(
        report_rt.label,
        Label::FlawWitnessed { counterexamples: 1 },
        "a FLAW denies CertifiedToSpecModuloInferred too"
    );
    assert_ne!(report_rt.label, Label::RustCertifiedToBinary);
    assert_ne!(report_rt.label, Label::SmtBackedToSpec);
    assert!(matches!(report_rt.label, Label::FlawWitnessed { .. }));
    // The divergence disclosure still surfaces the latent bug.
    assert_eq!(report_rt.divergence.latent_bugs, 1);
}

#[test]
fn test_badge_non_foundational_floor_yields_smt_backed() {
    // Foundational gate fails on the floor, but no FLAW and no external coupling:
    // the path is SMT-backed-to-spec, not certified, not flaw.
    let mut g = foundational_goodness();
    g.floor = FloorLevel::AxiomDependent;
    let report = compute_badge(
        Some(&g),
        Phase::StaticUniversal,
        &the_three_models(),
        &empty_inference(),
        &DivergenceClosure::new(),
    );
    assert_eq!(
        report.label,
        Label::SmtBackedToSpec,
        "non-foundational floor (no FLAW/coupling) => SmtBackedToSpec"
    );
}

#[test]
fn test_badge_externally_coupled_yields_intent_validated_only() {
    // Externally-coupled divergence blocks the auto-verdict: IntentValidatedOnly.
    let g = foundational_goodness();
    let divergence = DivergenceClosure::from_vec(vec![externally_coupled()]);
    let report = compute_badge(
        Some(&g),
        Phase::StaticUniversal,
        &the_three_models(),
        &empty_inference(),
        &divergence,
    );
    assert_eq!(
        report.label,
        Label::IntentValidatedOnly,
        "externally-coupled divergence => IntentValidatedOnly"
    );
}

#[test]
fn test_badge_goodness_none_yields_intent_validated_only() {
    // No proof-depth meter at all (None goodness) => IntentValidatedOnly.
    let report = compute_badge(
        None,
        Phase::StaticUniversal,
        &the_three_models(),
        &empty_inference(),
        &DivergenceClosure::new(),
    );
    assert_eq!(
        report.label,
        Label::IntentValidatedOnly,
        "None goodness => IntentValidatedOnly"
    );
}

#[test]
fn test_trusted_models_is_exactly_three_pins_the_exact_set() {
    // Positive regression test: the exact {isa, runtime, semantic_reflection}=true
    // set, nothing extra. MUST be revisited if a 4th trusted model is added.
    let exact = TrustedModels {
        isa: true,
        runtime: true,
        semantic_reflection: true,
    };
    assert!(exact.is_exactly_three());
    assert_eq!(exact, TrustedModels::all_three());

    // Any model missing breaks the exact-three predicate.
    for missing in [
        TrustedModels {
            isa: false,
            runtime: true,
            semantic_reflection: true,
        },
        TrustedModels {
            isa: true,
            runtime: false,
            semantic_reflection: true,
        },
        TrustedModels {
            isa: true,
            runtime: true,
            semantic_reflection: false,
        },
    ] {
        assert!(
            !missing.is_exactly_three(),
            "a missing model must break is_exactly_three"
        );
    }
}

#[test]
fn test_badge_report_serde_round_trip() {
    // A full BadgeReport must survive a JSON round-trip with the serde-mirror
    // floor (ProofFloor) intact — no String/bool desync.
    let g = foundational_goodness();
    let report = compute_badge(
        Some(&g),
        Phase::StaticUniversal,
        &the_three_models(),
        &nonempty_inference(),
        &DivergenceClosure::from_vec(vec![improvement()]),
    );
    let json = serde_json::to_string(&report).expect("BadgeReport should serialize");
    let back: crate::badge::BadgeReport =
        serde_json::from_str(&json).expect("BadgeReport should deserialize");

    assert_eq!(back.label, report.label);
    assert_eq!(back.phase, report.phase);
    let pd = back
        .proof_depth
        .expect("proof_depth present after round-trip");
    assert_eq!(pd.floor, ProofFloor::Foundational);
    assert!(pd.is_foundational(), "floor is the single source of truth");
    assert_eq!(back.inference.inferred_count, 1);
    assert_eq!(back.divergence.total, 1);
}

#[test]
fn test_enforcement_helper_runtime_observed_does_not_satisfy_certified() {
    // The enforcement helper (rail 6): a RuntimeObserved strength fails a
    // certified requirement when checked through the real ordering.
    use trust_ir_contract::{ProofStrength, ReasoningKind};
    let runtime = runtime_observed_strength();
    let certified = ProofStrength::certified(ReasoningKind::RuntimeMonitoring);
    assert!(
        !evidence_satisfies(&runtime, &certified),
        "runtime-observed evidence must not satisfy a certified requirement"
    );
    // And a certified strength satisfies an SMT-backed requirement (sanity).
    let smt_required = ProofStrength::smt_unsat();
    assert!(
        !evidence_satisfies(&runtime, &smt_required),
        "runtime-observed is not publication-grade, fails even SMT-backed reqs"
    );
}
