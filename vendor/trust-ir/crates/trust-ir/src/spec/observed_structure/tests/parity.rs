// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn empty_valid_and_explicit_modes_preserve_structural_scope_without_surface_authority() {
    assert!(run(&[]).0.is_empty());
    let mut specs = valid();
    assert!(run(&specs).0.is_empty());
    specs[0].enforcement = SpecEnforcementMode::Linked;
    let out = run(&specs).0;
    assert_eq!(out.len(), 2);
    assert!(
        out.iter()
            .all(|v| matches!(v, SpecLinkViolation::TypedTargetRequired { .. }))
    );
    specs[0].anchors[0].function = Some(FuncId::new(99));
    specs[0].anchors[0].projection_target = Some(SpecProjectionTarget::Function(FuncId::new(100)));
    assert!(run(&specs).0.is_empty());
}
#[test]
fn all_duplicate_names_are_exact_raw_nonblank_and_canonical_unique_sorted() {
    let mut specs = valid();
    specs[0].actions = vec![
        "z".into(),
        "z".into(),
        "a".into(),
        "a".into(),
        "z".into(),
        "\u{2003}".into(),
        "\u{2003}".into(),
    ];
    let variable = specs[0].vars[0].clone();
    let invariant = specs[0].invariants[0].clone();
    specs[0].vars.push(variable);
    specs[0].invariants.push(invariant);
    specs.push(specs[0].clone());
    specs.push(specs[0].clone());
    let out = run(&specs).0;
    assert_eq!(
        out.iter()
            .filter(|e| matches!(e, SpecLinkViolation::DuplicateMachineIdentity { .. }))
            .count(),
        1
    );
    assert_eq!(
        out.iter()
            .filter(|e| matches!(
                e,
                SpecLinkViolation::DuplicateMemberIdentity {
                    member: "action",
                    ..
                }
            ))
            .count(),
        2
    );
}
#[test]
fn blank_unicode_semantic_fields_keep_exact_container_subject_and_field() {
    let mut spec = SpecModule::new("\u{2003}\t");
    spec.actions = vec!["\n".into()];
    spec.vars = vec![SpecVar::new("\u{2002}", "\t")];
    spec.invariants = vec![SpecInvariant::new("", "\u{3000}")];
    spec.origin = SpecOrigin::External("\r".into());
    spec.anchors.push(anchor("", ""));
    spec.anchors[0].rust_symbol = " ".into();
    spec.waivers.push(waiver("", ""));
    spec.waivers[0].reason = " ".into();
    spec.proofs.push(proof("", ""));
    spec.proofs[0].proof_name = " ".into();
    let out = run(&[spec]).0;
    assert!(
        out.iter()
            .all(|v| matches!(v, SpecLinkViolation::BlankSemanticValue { .. }))
    );
    assert!(out.len() >= 10);
}
#[test]
fn known_foreign_missing_foreign_and_duplicate_ambiguous_targets_keep_original_resolution() {
    let mut specs = valid();
    specs[0].anchors = vec![
        anchor("N", "missing"),
        anchor("Gone", "a"),
        anchor("M", "missing"),
    ];
    specs[0].waivers.push(waiver("Gone", "a"));
    specs[0].proofs.push(proof("Gone", "a"));
    let mut n = SpecModule::new("N");
    n.actions = vec!["a".into()];
    specs.push(n);
    let out = run(&specs).0;
    assert_eq!(
        out.iter()
            .filter(|v| matches!(v, SpecLinkViolation::ReferenceContainerMismatch { .. }))
            .count(),
        1
    );
    assert_eq!(
        out.iter()
            .filter(|v| matches!(v, SpecLinkViolation::MachineMissing { .. }))
            .count(),
        3
    );
    assert_eq!(
        out.iter()
            .filter(|v| matches!(v, SpecLinkViolation::ActionMissing { .. }))
            .count(),
        1
    );
    specs.push(specs[0].clone());
    let out = run(&specs).0;
    assert!(
        !out.iter()
            .any(|v| matches!(v,SpecLinkViolation::ActionMissing{machine,..} if machine=="M"))
    );
}
#[test]
fn anchor_identity_function_precedence_and_exact_debug_spelling_match_original() {
    let mut specs = valid();
    let a = &mut specs[0].anchors[0];
    a.action = "a'\"\n".into();
    a.function = Some(FuncId::new(u32::MAX));
    specs[0].actions = vec!["a'\"\n".into()];
    let mut b = specs[0].anchors[0].clone();
    b.rust_symbol = "different".into();
    specs[0].anchors.extend([b.clone(), b]);
    let out = run(&specs).0;
    assert!(out.iter().any(|v|matches!(v,SpecLinkViolation::DuplicateBindingIdentity{binding:"anchor",identity,..} if identity==&format!("{:?} -> function #{}","a'\"\n",u32::MAX))));
    specs[0].anchors[0].function = None;
    run(&specs);
}
#[test]
fn waiver_conflict_and_proof_tag_identity_ignore_only_original_opaque_payloads() {
    let mut specs = valid();
    specs[0].waivers = vec![waiver("M", "a"), waiver("M", "a"), waiver("M", "a")];
    let mut a = proof("M", "a");
    a.kind = ProofKind::CleanTheorem { name: "one".into() };
    let mut b = a.clone();
    b.kind = ProofKind::CleanTheorem {
        name: "different".repeat(1000),
    };
    specs[0].proofs = vec![a, b];
    let out = run(&specs).0;
    assert_eq!(
        out.iter()
            .filter(|v| matches!(v, SpecLinkViolation::DuplicateBindingIdentity { .. }))
            .count(),
        2
    );
    assert_eq!(
        out.iter()
            .filter(|v| matches!(v, SpecLinkViolation::AnchorWaiverConflict { .. }))
            .count(),
        1
    );
}
#[test]
fn projection_scheme_origin_target_and_owned_blank_presence_are_separate_rules() {
    let mut specs = valid();
    specs[0].anchors[0].projection_target = Some(SpecProjectionTarget::TemporalFieldPathsV1);
    specs[0].anchors[0].project = None;
    let out = run(&specs).0;
    assert_eq!(out.len(), 2);
    specs[0].anchors[0].project = Some(TEMPORAL_FIELD_PATH_PROJECTION_V1.into());
    assert!(run(&specs).0.is_empty());
    specs[0].anchors[0].projection_target = Some(SpecProjectionTarget::ExternalUnresolved);
    assert_eq!(run(&specs).0.len(), 1);
    specs[0].origin = SpecOrigin::External("model".into());
    assert!(run(&specs).0.is_empty());
    specs[0].anchors[0].project = Some("\u{2003}".into());
    assert_eq!(run(&specs).0.len(), 1);
}
#[test]
fn all_temporal_forms_preserve_single_state_vs_action_relation_and_fairness_names() {
    for kind in 0..5 {
        let mut specs = valid();
        let p = formula(ClausePlace::SpecVarNext { index: 0 }, ClauseSort::Int);
        let form = match kind {
            0 => TemporalForm::Always(p),
            1 => TemporalForm::Eventually(p),
            2 => TemporalForm::LeadsTo(p.clone(), p),
            3 => TemporalForm::WeakFair {
                action: "a".into(),
                relation: Some(p),
            },
            _ => TemporalForm::StrongFair {
                action: "missing".into(),
                relation: Some(p),
            },
        };
        specs[0].temporal.push(SpecTemporal::new("T", form));
        let out = run(&specs).0;
        assert_eq!(
            out.iter()
                .any(|v| matches!(v, SpecLinkViolation::SpecTypedBindingInvalid { .. })),
            kind < 3
        );
        assert_eq!(
            out.iter().any(|v| matches!(
                v,
                SpecLinkViolation::ActionMissing {
                    from: "temporal",
                    ..
                }
            )),
            kind == 4
        );
    }
}
#[test]
fn declared_sort_parsed_fallback_and_first_spelled_variable_preserve_both_binding_errors() {
    let mut specs = valid();
    specs[0].vars = vec![
        SpecVar::new("other", "Int"),
        SpecVar::new("x", "BitVec(8)").with_sort(ClauseSort::BitVec(16)),
        SpecVar::new("x", "Int"),
    ];
    specs[0].invariants[0].typed = Some(formula(
        ClausePlace::SpecVar { index: 0 },
        ClauseSort::BitVec(32),
    ));
    let out = run(&specs).0;
    assert!(
        out.iter()
            .any(|v| matches!(v, SpecLinkViolation::SpecVariableSortMismatch { .. }))
    );
    assert_eq!(
        out.iter()
            .filter(|v| matches!(v, SpecLinkViolation::SpecTypedBindingInvalid { .. }))
            .count(),
        2
    );
}
#[test]
fn all_function_places_and_missing_indices_keep_full_exact_debug_reasons() {
    for place in [
        ClausePlace::Param { index: u32::MAX },
        ClausePlace::ResultSlot { index: 2 },
        ClausePlace::MutParamExit { index: 3 },
        ClausePlace::World,
        ClausePlace::Unwind,
        ClausePlace::Value(ValueId::new(u32::MAX)),
        ClausePlace::WorldPre,
        ClausePlace::WorldPost,
        ClausePlace::ParamPointeeEntry { index: 4 },
        ClausePlace::SpecVar { index: u32::MAX },
    ] {
        let mut specs = valid();
        specs[0].invariants[0].typed = Some(formula(place, ClauseSort::Int));
        let out = run(&specs).0;
        assert_eq!(out.len(), 1);
    }
}
#[test]
fn recursive_array_datatype_sort_mismatches_preserve_full_derived_debug_and_equality() {
    let mut specs = valid();
    specs[0].vars[0].sort = Some(deep_sort());
    specs[0].vars[0].ty = "opaque".into();
    specs[0].invariants[0].typed = Some(formula(ClausePlace::SpecVar { index: 0 }, deep_sort()));
    assert!(run(&specs).0.is_empty());
    let p = specs[0].invariants[0].typed.as_mut().unwrap();
    p.bindings[0].1.sort = ClauseSort::Array(Box::new(ClauseSort::Int), Box::new(ClauseSort::Bool));
    let out = run(&specs).0;
    assert_eq!(out.len(), 1);
    assert!(
        matches!(&out[0],SpecLinkViolation::SpecTypedBindingInvalid{detail,..} if detail.contains("Datatype")&&detail.contains("Array(Int, Bool)"))
    );
}
#[test]
fn formula_payload_schema_rendering_and_irrelevant_theorem_span_payloads_remain_opaque() {
    let mut specs = valid();
    let (_, before) = run(&specs);
    let p = specs[0].invariants[0].typed.as_mut().unwrap();
    p.payload = "opaque".repeat(10000);
    p.schema = "opaque".repeat(10000);
    p.smtlib = Some("opaque".repeat(10000));
    p.sort = Some("opaque".repeat(10000));
    specs[0].anchors[0].span = "opaque".repeat(10000);
    let (_, after) = run(&specs);
    assert_eq!(before.events, after.events);
}
#[test]
fn unicode_full_tail_reference_details_and_final_deduplication_are_exact_owned_results() {
    let mut specs = valid();
    specs[0].anchors = vec![anchor("Gone", "a"), anchor("Gone", "a")];
    specs[0].anchors[0].rust_symbol = "λ'\"\n\0".repeat(1000) + "TAIL";
    specs[0].anchors[1] = specs[0].anchors[0].clone();
    let out = run(&specs).0;
    assert_eq!(out.len(), 1);
    assert!(
        matches!(&out[0],SpecLinkViolation::MachineMissing{detail,..} if detail.contains("TAIL"))
    );
    let old = out.clone();
    specs.clear();
    assert_eq!(out, old);
}
