// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn actual_full_module_selector_and_original_attachment_loop_match_on_all_families() {
    let b = fixture();
    for index in 0..b.requests.len() {
        observed(&b, index);
    }
}
#[test]
fn out_of_range_actual_request_index_is_typed_invalidrange_not_empty_success() {
    let b = fixture();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    for index in [b.requests.len(), usize::MAX] {
        assert_eq!(
            b.request_certificate_errors_observed(index, &mut s, site()),
            Err(ObservedValueError::InvalidRange)
        );
    }
    assert!(s.first_refusal().is_none());
}
#[test]
fn physical_duplicate_pair_known_digest_requested_lineage_and_suite_errors_keep_order() {
    let b = bad();
    let rows = observed(&b, 0).0;
    assert!(matches!(
        rows.as_slice(),
        [
            E::CertificateDigestMismatch { .. },
            E::CertificateObligationNotRequested { .. },
            E::CertificateNotInLineage { .. },
            E::DuplicateRequestCertificate { .. },
            E::CertificateDigestMismatch { .. },
            E::CertificateObligationNotRequested { .. },
            E::CertificateNotInLineage { .. },
            E::MissingCertificate { .. },
            E::CertificateObligationNotRequested { .. },
            E::CertificateNotInLineage { .. },
            E::CertificateVerifierSuiteMismatch { .. }
        ]
    ));
}
#[test]
fn duplicate_attachment_key_ignores_digest_but_keeps_raw_obligation_and_prover() {
    let mut b = fixture();
    let c = vc(&mut b).certificates[0].clone();
    let mut different = c.clone();
    different.evidence_digest = ProofDigest::sha256([8; 32]);
    vc(&mut b).certificates = vec![c, different];
    let rows = observed(&b, 0).0;
    assert_eq!(
        rows.iter()
            .filter(|e| matches!(e, E::DuplicateRequestCertificate { .. }))
            .count(),
        1
    );
}
#[test]
fn full_known_selector_matches_actual_evidence_bytes_not_only_prover_or_obligation() {
    let mut b = fixture();
    assert!(observed(&b, 0).0.is_empty());
    b.module.proof_certificates[0].evidence =
        ProofEvidence::LeanProof("changed actual evidence".into());
    let rows = observed(&b, 0).0;
    assert!(
        rows.iter()
            .any(|e| matches!(e, E::CertificateDigestMismatch { .. }))
    );
    assert!(
        !rows
            .iter()
            .any(|e| matches!(e, E::MissingCertificate { .. }))
    );
}
#[test]
fn same_digest_bytes_with_other_algorithm_are_raw_mismatch() {
    let mut b = fixture();
    vc(&mut b).certificates[0].evidence_digest.algorithm = ProofDigestAlgorithm::TrustIrStableV1;
    assert!(
        observed(&b, 0)
            .0
            .iter()
            .any(|e| matches!(e, E::CertificateDigestMismatch { .. }))
    );
}
#[test]
fn raw_case_separator_unicode_and_nul_provers_never_alias_known_pairs() {
    for name in ["TRUST-VC", "trust-vc", "λ\0尾", "é", "e\u{301}"] {
        let mut b = fixture();
        vc(&mut b).certificates[0].prover = name.into();
        let rows = observed(&b, 0).0;
        assert!(
            rows.iter()
                .any(|e| matches!(e, E::MissingCertificate { .. }))
        );
        assert!(
            !rows
                .iter()
                .any(|e| matches!(e, E::CertificateDigestMismatch { .. }))
        );
    }
}
#[test]
fn long_equal_length_provers_with_last_byte_difference_stay_distinct() {
    let mut b = fixture();
    let name = "a".repeat(4096) + "x";
    b.module.proof_certificates[0].prover = name.clone();
    let mut r = b.module.proof_certificates[0].lineage_ref();
    r.prover = "a".repeat(4096) + "y";
    vc(&mut b).certificates = vec![r];
    assert!(
        observed(&b, 0)
            .0
            .iter()
            .any(|e| matches!(e, E::MissingCertificate { .. }))
    );
}
#[test]
fn duplicate_module_selectors_preserve_set_membership_and_full_actual_owned_index() {
    let mut b = fixture();
    let duplicate = b.module.proof_certificates[0].clone();
    b.module
        .proof_certificates
        .extend([duplicate.clone(), duplicate]);
    observed(&b, 0);
}
#[test]
fn requested_obligation_duplicates_and_unsorted_order_are_membership_only_here() {
    let mut b = fixture();
    vc(&mut b).obligations = vec![ProofId::new(9), ProofId::new(0), ProofId::new(0)];
    assert!(
        !observed(&b, 0)
            .0
            .iter()
            .any(|e| matches!(e, E::CertificateObligationNotRequested { .. }))
    );
}
#[test]
fn source_bound_membership_uses_whole_actual_certificate_reference() {
    let mut b = fixture();
    b.lineage.nodes[0].certificates[0].evidence_digest = ProofDigest::sha256([3; 32]);
    let rows = observed(&b, 0).0;
    assert!(
        rows.iter()
            .any(|e| matches!(e, E::CertificateNotInLineage { .. }))
    );
    assert!(!rows.iter().any(|e| matches!(
        e,
        E::CertificateDigestMismatch { .. } | E::MissingCertificate { .. }
    )));
}
#[test]
fn actual_source_filter_rejects_other_source_while_none_preserves_old_unfiltered_sets() {
    let mut b = fixture();
    b.input = NativeAdapterInput::RustMir {
        body_digest: ProofDigest::sha256([55; 32]),
    };
    assert!(
        observed(&b, 0)
            .0
            .iter()
            .any(|e| matches!(e, E::CertificateNotInLineage { .. }))
    );
    b.input = NativeAdapterInput::TrustIrModule;
    assert!(
        !observed(&b, 0)
            .0
            .iter()
            .any(|e| matches!(e, E::CertificateNotInLineage { .. }))
    );
}
#[test]
fn empty_and_punctuation_provers_keep_existing_suite_refusal_semantics() {
    for name in ["", "!!!", "trust-vc", "TRUST_VC"] {
        let mut b = fixture();
        vc(&mut b).certificates[0].prover = name.into();
        observed(&b, 0);
    }
}
#[test]
fn full_returned_raw_prover_and_canonical_names_outlive_original_bundle() {
    let mut b = fixture();
    vc(&mut b).certificates[0].prover = "wrong λ\0尾".repeat(900);
    let expected = ordinary(&b, 0);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let rows = b
        .request_certificate_errors_observed(0, &mut s, site())
        .unwrap();
    drop(b);
    assert_eq!(rows, expected);
    retire_native_bundle_errors_observed(rows, &mut s, site()).unwrap();
}
#[test]
fn no_module_certificate_still_checks_every_other_attachment_diagnostic() {
    let mut b = bad();
    b.module.proof_certificates.clear();
    let rows = observed(&b, 0).0;
    assert_eq!(
        rows.iter()
            .filter(|e| matches!(e, E::MissingCertificate { .. }))
            .count(),
        3
    );
    assert!(
        rows.iter()
            .any(|e| matches!(e, E::DuplicateRequestCertificate { .. }))
    );
    assert!(
        rows.iter()
            .any(|e| matches!(e, E::CertificateVerifierSuiteMismatch { .. }))
    );
}
#[test]
fn successful_selector_data_is_not_discharged_or_replayed_authority() {
    let b = fixture();
    assert!(observed(&b, 0).0.is_empty());
    assert!(
        b.request_errors_original_for_observed_tests()
            .iter()
            .any(|e| matches!(e, E::TrustVcCertificateNotDischarged { .. }))
    );
}
