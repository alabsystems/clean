// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn exact_valid_inner_success_matches_original_without_minting_any_authority() {
    let b = good();
    assert_eq!(b.validate(), Ok(()));
    assert_eq!(observed(&b).0, Ok(()));
}
#[test]
fn exact_valid_inner_success_includes_real_supplied_mc_and_wp_evidence() {
    let b = with_evidence();
    assert_eq!(b.validate(), Ok(()));
    assert_eq!(observed(&b).0, Ok(()));
}
#[test]
fn whole_invalid_result_preserves_all_original_groups_and_exact_order() {
    let b = bad();
    let rows = observed(&b).0.unwrap_err();
    assert!(matches!(rows.first(), Some(E::UnsupportedSchemaVersion(_))));
    let request = rows
        .iter()
        .position(|e| matches!(e, E::InvalidTrustMcChcOptions { .. }))
        .unwrap();
    let evidence = rows
        .iter()
        .position(|e| matches!(e, E::EvidenceRequestDigestMismatch { .. }))
        .unwrap();
    assert!(request < evidence);
    assert!(rows[..request].iter().any(|e| matches!(e, E::Lineage(_))));
}
#[test]
fn whole_original_raw_vc_request_is_rejected_despite_strong_public_status() {
    let b = crate::request::tests::native_bundle();
    assert!(observed(&b).0.unwrap_err().iter().any(|e| matches!(
        e,
        E::TrustVcCertificateNotDischarged {
            status: ProofStatus::Discharged,
            ..
        }
    )));
}
#[test]
fn unencodable_module_keeps_wire_errors_without_panicking_or_inventing_digest() {
    let mut b = bad();
    b.module.types.push(Ty::Error);
    b.module.completeness = Some(ModuleCompleteness::Complete);
    let rows = observed(&b).0.unwrap_err();
    assert!(
        rows.iter()
            .any(|e| matches!(e, E::TrustIrModuleHasNoWireIdentity { .. }))
    );
    assert!(
        !rows
            .iter()
            .any(|e| matches!(e, E::TrustIrModuleDigestMismatch { .. }))
    );
}
#[test]
fn source_digest_and_module_identity_are_independent_real_inputs() {
    let mut b = good();
    b.input = NativeAdapterInput::RustMir {
        body_digest: ProofDigest::sha256([0; 32]),
    };
    let rows = observed(&b).0.unwrap_err();
    assert!(rows.iter().any(|e| matches!(
        e,
        E::EmptyDigest {
            field: "input.rust_mir.body_digest"
        }
    )));
    assert!(
        !rows
            .iter()
            .any(|e| matches!(e, E::TrustIrModuleDigestMismatch { .. }))
    );
}
#[test]
fn empty_request_list_is_inner_diagnostic_failure_not_operational_success_shortcut() {
    let mut b = good();
    b.requests.clear();
    b.evidence_bundles.clear();
    assert!(observed(&b).0.unwrap_err().contains(&E::EmptyRequests));
}
#[test]
fn missing_evidence_is_not_invented_as_a_new_original_validation_requirement() {
    let b = good();
    assert!(b.evidence_bundles.is_empty());
    assert_eq!(observed(&b).0, Ok(()));
}
#[test]
fn duplicate_last_request_evidence_binding_remains_the_actual_original_result() {
    let mut b = with_evidence();
    let mut last = b.requests[0].clone();
    if let NativeVerificationRequest::TrustMc(r) = &mut last {
        r.provenance.expected_verifier.name = "different-last".into();
    }
    b.requests.push(last);
    let rows = observed(&b).0.unwrap_err();
    assert!(rows.iter().any(|e| matches!(e, E::DuplicateRequestId(_))));
    assert!(
        rows.iter()
            .any(|e| matches!(e, E::EvidenceRequestDigestMismatch { .. }))
    );
}
#[test]
fn full_unsigned_schema_and_raw_unicode_errors_survive_whole_source_drop() {
    let result = {
        let mut b = bad();
        b.module.functions[0].name = "raw 'λ\0尾".repeat(300);
        b.module.functions[0].blocks[0]
            .body
            .push(crate::InstrNode::new(crate::Inst::Borrow {
                ptr: crate::ValueId::new(0),
            }));
        observed(&b).0
    };
    let rows = result.unwrap_err();
    assert!(rows.contains(&E::UnsupportedSchemaVersion(u32::MAX)));
    assert!(
        rows.iter()
            .any(|e| matches!(e, E::RustReferenceAsPermissionBorrow { .. }))
    );
}
#[test]
fn three_actual_group_results_concatenate_to_the_complete_ordinary_error_vector() {
    let b = bad();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut expected = b.pre_request_errors_observed(&mut s, site()).unwrap();
    expected.extend(
        b.request_errors_kernel_less_observed(&mut s, site())
            .unwrap(),
    );
    expected.extend(b.evidence_errors_observed(&mut s, site()).unwrap());
    assert_eq!(Err::<(), _>(expected.clone()), b.validate());
    retire_native_bundle_errors_observed(expected, &mut s, site()).unwrap();
}
#[test]
fn success_and_failure_inner_results_have_distinct_owning_caller_retirement() {
    for b in [good(), bad()] {
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let result = b.validate_kernel_less_observed(&mut s, site()).unwrap();
        assert_eq!(result.is_ok(), b.validate().is_ok());
        NativeVerificationBundle::retire_kernel_less_validation_observed(result, &mut s, site())
            .unwrap();
        let last = o.events.last().unwrap();
        assert_eq!(
            (last.phase, last.work, last.copy_bytes),
            (ExecutionPhase::Publication, 0, 0)
        );
    }
}
