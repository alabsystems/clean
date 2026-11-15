// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn all_three_real_request_evidence_families_match_the_complete_original() {
    let b = good();
    assert!(observed(&b).0.is_empty());
}
#[test]
fn all_nine_real_modes_match_the_complete_original_leaf() {
    for r in all_modes() {
        let mut b = good();
        b.requests = vec![r];
        b.evidence_bundles = vec![evidence(&b.requests[0], b.trust_ir_module_digest)];
        observed(&b);
    }
}
#[test]
fn empty_evidence_list_is_exact_success_without_other_bundle_validation() {
    let mut b = good();
    b.requests.clear();
    b.evidence_bundles.clear();
    assert!(observed(&b).0.is_empty());
}
#[test]
fn unknown_request_continues_before_any_child_even_with_bad_metadata() {
    let mut b = bad();
    let mut e = b.evidence_bundles.remove(1);
    mc(&mut e).request = NativeRequestId::new(999);
    b.evidence_bundles = vec![e];
    assert_eq!(
        observed(&b).0,
        vec![E::EvidenceRequestUnknown {
            request: NativeRequestId::new(999),
            suite: Suite::TrustMc
        }]
    );
}
#[test]
fn duplicate_unknown_request_reports_duplicate_then_unknown_on_every_repeat() {
    let mut b = bad();
    let mut e = b.evidence_bundles.remove(1);
    mc(&mut e).request = NativeRequestId::new(999);
    b.evidence_bundles = vec![e.clone(), e.clone(), e];
    let (rows, _, _) = observed(&b);
    assert_eq!(rows.len(), 5);
    assert!(matches!(&rows[1], E::DuplicateEvidenceBundle { .. }));
    assert!(matches!(&rows[2], E::EvidenceRequestUnknown { .. }));
}
#[test]
fn duplicate_key_includes_mode_so_distinct_modes_are_not_duplicates() {
    let mut b = good();
    let a = b.evidence_bundles[1].clone();
    let mut c = a.clone();
    mc(&mut c).mode = TrustMcVerificationMode::Pdr;
    b.evidence_bundles = vec![a, c];
    let (rows, _, _) = observed(&b);
    assert!(
        !rows
            .iter()
            .any(|e| matches!(e, E::DuplicateEvidenceBundle { .. }))
    );
    assert!(
        rows.iter()
            .any(|e| matches!(e, E::EvidenceRequestMismatch { .. }))
    );
}
#[test]
fn duplicate_key_includes_variant_even_when_ids_and_mode_tags_match() {
    let mut b = good();
    let id = b.evidence_bundles[1].request();
    if let NativeEvidenceBundle::TrustVc(v) = &mut b.evidence_bundles[0] {
        v.request = id;
        v.mode = TrustVcVerificationMode::MergeProofCertificates;
    }
    b.evidence_bundles.truncate(2);
    let (rows, _, _) = observed(&b);
    assert!(
        !rows
            .iter()
            .any(|e| matches!(e, E::DuplicateEvidenceBundle { .. }))
    );
}
#[test]
fn last_duplicate_request_row_controls_digest_and_provenance() {
    let mut b = minimal();
    let mut later = b.requests[0].clone();
    provenance(&mut later).expected_verifier.name = "different-last".into();
    b.requests.push(later);
    let (rows, _, _) = observed(&b);
    assert!(
        rows.iter()
            .any(|e| matches!(e, E::EvidenceRequestDigestMismatch { .. }))
    );
    assert!(rows.iter().any(|e| matches!(
        e,
        E::EvidenceProvenanceMismatch {
            field: "verifier",
            ..
        }
    )));
}
#[test]
fn later_exact_request_replaces_earlier_wrong_record() {
    let mut b = good();
    let correct = b.requests[1].clone();
    provenance(&mut b.requests[1]).expected_verifier.name = "wrong-first".into();
    b.requests.push(correct);
    assert!(observed(&b).0.is_empty());
}
#[test]
fn mode_and_module_and_request_digest_mismatches_are_independent() {
    let mut b = good();
    let m = mc(&mut b.evidence_bundles[1]);
    m.mode = TrustMcVerificationMode::Pdr;
    m.trust_ir_module_digest = ProofDigest::sha256([77; 32]);
    m.request_digest = ProofDigest::sha256([78; 32]);
    let (rows, _, _) = observed(&b);
    assert!(
        rows.iter()
            .any(|e| matches!(e, E::EvidenceRequestMismatch { .. }))
    );
    assert!(
        rows.iter()
            .any(|e| matches!(e, E::EvidenceTrustIrModuleDigestMismatch { .. }))
    );
    assert!(
        rows.iter()
            .any(|e| matches!(e, E::EvidenceRequestDigestMismatch { .. }))
    );
}
#[test]
fn all_metadata_obligation_and_artifact_children_remain_in_original_order() {
    let b = bad();
    let (rows, _, _) = observed(&b);
    assert_eq!(rows, ordinary(&b));
    assert!(rows.len() > 20);
}
#[test]
fn solver_empty_and_each_actual_solver_validation_are_distinct_checks() {
    let mut b = good();
    mc(&mut b.evidence_bundles[1]).solvers = vec![
        NativeToolIdentity::new(" ").with_version(" "),
        NativeToolIdentity::new(" ").with_revision(" "),
    ];
    let (rows, _, _) = observed(&b);
    assert_eq!(
        rows.iter()
            .filter(|e| matches!(e, E::EmptyProvenanceField("evidence.solvers")))
            .count(),
        2
    );
    assert_eq!(
        rows.iter()
            .filter(|e| matches!(
                e,
                E::InvalidToolIdentityField {
                    field: "evidence.solvers",
                    ..
                }
            ))
            .count(),
        2
    );
    mc(&mut b.evidence_bundles[1]).solvers.clear();
    let (rows, _, _) = observed(&b);
    assert_eq!(
        rows.iter()
            .filter(|e| matches!(e, E::EmptyProvenanceField("evidence.solvers")))
            .count(),
        1
    );
}
#[test]
fn expected_raw_identity_mismatch_does_not_hide_suite_or_replay_metadata_errors() {
    let b = bad();
    let (rows, _, _) = observed(&b);
    assert!(
        rows.iter()
            .any(|e| matches!(e, E::ExpectedVerifierIdentityMismatch { .. }))
    );
    assert!(
        rows.iter()
            .any(|e| matches!(e, E::ReplayIdentityVerifierSuiteMismatch { .. }))
    );
}
#[test]
fn repeated_artifacts_keep_full_diagnostic_multiplicity() {
    let b = bad();
    let (rows, _, _) = observed(&b);
    assert!(
        rows.iter()
            .any(|e| matches!(e, E::DuplicateEvidenceArtifact { .. }))
    );
    assert!(
        rows.iter()
            .filter(|e| matches!(e, E::InvalidEvidenceArtifact { .. }))
            .count()
            >= 6
    );
}
#[test]
fn full_names_and_whole_diagnostic_list_outlive_original_bundle() {
    let b = bad();
    let expected = ordinary(&b);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = b.evidence_errors_observed(&mut s, site()).unwrap();
    drop(b);
    assert_eq!(rows, expected);
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
}
#[test]
fn this_pass_does_not_replace_full_request_or_module_or_lineage_validation() {
    let mut b = good();
    b.schema_version = 0;
    b.lineage.nodes.clear();
    b.module.functions.clear();
    assert!(observed(&b).0.is_empty());
    assert!(b.validate().is_err());
}
