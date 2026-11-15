// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn complete_actual_original_prefix_is_exact_with_only_empty_requests_outstanding() {
    assert_eq!(observed(&clean()).0, vec![E::EmptyRequests]);
}
#[test]
fn every_original_group_keeps_whole_diagnostics_and_actual_outer_order() {
    let b = bad();
    let rows = observed(&b).0;
    let position = |p: fn(&E) -> bool| rows.iter().position(p).unwrap();
    let schema = position(|e| matches!(e, E::UnsupportedSchemaVersion(_)));
    let wire = position(|e| matches!(e, E::TrustIrModuleHasNoWireIdentity { .. }));
    let reference = position(|e| matches!(e, E::RustReferenceAsPermissionBorrow { .. }));
    let source = position(|e| {
        matches!(
            e,
            E::EmptyDigest {
                field: "input.rust_mir.body_digest"
            }
        )
    });
    let requests = position(|e| matches!(e, E::EmptyRequests));
    let provenance = position(|e| matches!(e, E::EmptyProvenanceField(_)));
    let serialization = position(|e| matches!(e, E::NonCanonicalSerialization(_)));
    let diagnostics = position(|e| matches!(e, E::InvalidBundleDiagnosticsPolicy { .. }));
    let lineage = position(|e| matches!(e, E::Lineage(_)));
    let formula = position(|e| matches!(e, E::FormulaTextsDisagree { .. }));
    let digest = position(|e| matches!(e, E::SourceDigestNotInLineage(_)));
    assert!(
        schema < wire
            && wire < reference
            && reference < source
            && source < requests
            && requests < provenance
            && provenance < serialization
            && serialization < diagnostics
            && diagnostics < lineage
            && lineage < formula
            && formula < digest
    );
    assert!(rows.len() > digest + 1);
}
#[test]
fn source_none_branch_uses_adapter_input_not_provenance_source_digest() {
    let mut b = clean();
    b.input = NativeAdapterInput::TrustIrModule;
    b.provenance.source_digest = Some(ProofDigest {
        algorithm: ProofDigestAlgorithm::TrustIrStableV1,
        bytes: [0; 32],
    });
    let rows = observed(&b).0;
    assert!(!rows.iter().any(|e| matches!(
        e,
        E::EmptyDigest {
            field: "input.rust_mir.body_digest"
        } | E::NonCryptographicDigest {
            field: "input.source_digest"
        } | E::SourceDigestNotInLineage(_)
    )));
}
#[test]
fn two_independent_actual_source_guards_keep_both_errors_for_zero_legacy() {
    let mut b = clean();
    b.input = NativeAdapterInput::RustMir {
        body_digest: ProofDigest {
            algorithm: ProofDigestAlgorithm::TrustIrStableV1,
            bytes: [0; 32],
        },
    };
    let rows = observed(&b).0;
    let z = rows
        .iter()
        .position(|e| {
            matches!(
                e,
                E::EmptyDigest {
                    field: "input.rust_mir.body_digest"
                }
            )
        })
        .unwrap();
    assert!(matches!(
        &rows[z + 1],
        E::NonCryptographicDigest {
            field: "input.source_digest"
        }
    ));
    assert!(matches!(&rows[z + 2], E::EmptyRequests));
}
#[test]
fn lineage_against_errors_stay_one_whole_group_before_formula_errors() {
    let b = bad();
    let rows = observed(&b).0;
    let at = rows
        .iter()
        .position(|e| matches!(e, E::Lineage(_)))
        .unwrap();
    let E::Lineage(actual) = &rows[at] else {
        panic!("lineage");
    };
    assert_eq!(
        actual,
        &b.lineage
            .validate_against(&b.module.proof_obligations, &b.module.proof_certificates)
            .unwrap_err()
    );
    assert!(matches!(&rows[at + 1], E::FormulaTextsDisagree { .. }));
}
#[test]
fn exact_serialization_and_bundle_policy_child_error_order_is_retained() {
    let b = bad();
    let rows = observed(&b).0;
    let serial: Vec<_> = rows
        .iter()
        .filter(|e| matches!(e, E::NonCanonicalSerialization(_)))
        .cloned()
        .collect();
    assert_eq!(
        serial,
        vec![
            E::NonCanonicalSerialization("serialization.canonical_order"),
            E::NonCanonicalSerialization("serialization.sort_unordered_sets"),
            E::NonCanonicalSerialization("serialization.messagepack_named_fields")
        ]
    );
}
#[test]
fn physical_repeated_formula_carriers_and_raw_reference_locations_are_not_deduped() {
    let mut b = bad();
    let mut second = b.module.proof_obligations[0].clone();
    second.id = ProofId::new(8);
    b.module.proof_obligations.push(second);
    b.lineage.nodes[0].obligations.push(ProofId::new(8));
    let rows = observed(&b).0;
    assert_eq!(
        rows.iter()
            .filter(|e| matches!(e, E::FormulaTextsDisagree { .. }))
            .count(),
        2
    );
    assert!(rows.iter().any(|e|matches!(e,E::RustReferenceAsPermissionBorrow{location}if location=="function 'raw 'λ\0尾' bb0 #0")));
}
#[test]
fn late_compiler_fact_diagnostics_are_not_lost_after_earlier_groups_fail() {
    let b = bad();
    let all = observed(&b).0;
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let tail = b.compiler_fact_errors_observed(&mut s, site()).unwrap();
    assert!(!tail.is_empty());
    assert!(all.ends_with(&tail));
    retire_native_bundle_errors_observed(tail, &mut s, site()).unwrap();
}
#[test]
fn matching_prefix_does_not_issue_a_module_or_bundle_authority() {
    let b = clean();
    let rows = observed(&b).0;
    assert_eq!(rows, vec![E::EmptyRequests]);
    assert!(b.validate().is_err());
}
#[test]
fn complete_owned_ordered_errors_outlive_the_original_bundle() {
    let b = bad();
    let expected = ordinary(&b);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = b.pre_request_errors_observed(&mut s, site()).unwrap();
    drop(b);
    assert_eq!(rows, expected);
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
}
#[test]
fn full_u32_schema_ids_and_count_fields_are_preserved_in_outer_child_results() {
    let mut b = clean();
    b.schema_version = u32::MAX;
    b.serialization.schema_version = u32::MAX;
    b.lineage.schema_version = u32::MAX;
    let rows = observed(&b).0;
    assert_eq!(rows[0], E::UnsupportedSchemaVersion(u32::MAX));
    assert!(
        rows.iter()
            .any(|e| matches!(e,E::UnsupportedSerializationSchemaVersion(v)if *v==u32::MAX))
    );
    assert!(rows.iter().any(|e|matches!(e,E::Lineage(es)if es.iter().any(|e|matches!(e,ProofLineageError::UnsupportedSchemaVersion(v)if *v==u32::MAX)))));
}
#[test]
fn source_target_lineage_membership_can_match_different_actual_physical_nodes() {
    let mut b = clean();
    let mut extra = b.lineage.nodes[0].clone();
    extra.id = crate::ProofLineageId::new(1);
    extra.source_module = ProofDigest::sha256([9; 32]);
    b.lineage.nodes[0].target_module = ProofDigest::sha256([8; 32]);
    b.lineage.nodes.push(extra);
    let rows = observed(&b).0;
    assert!(!rows.iter().any(|e| matches!(
        e,
        E::SourceDigestNotInLineage(_) | E::TrustIrDigestNotInLineage(_)
    )));
}
#[test]
fn empty_and_absent_optional_children_still_complete_the_actual_ordered_walk() {
    let mut b = clean();
    b.provenance.toolchain.clear();
    b.module.proof_obligations[0].formula = None;
    b.compiler_facts = crate::request::NativeCompilerFacts::default();
    b.trust_ir_module_digest = b.module.stable_digest();
    b.lineage.nodes[0].target_module = b.trust_ir_module_digest;
    observed(&b);
}
#[test]
fn reference_stamp_is_actual_producer_data_and_never_an_input_language_fallback() {
    let mut b = bad();
    b.module.functions[0].producer = Some(Producer::TrustIr);
    let rows = observed(&b).0;
    assert!(
        !rows
            .iter()
            .any(|e| matches!(e, E::RustReferenceAsPermissionBorrow { .. }))
    );
}
