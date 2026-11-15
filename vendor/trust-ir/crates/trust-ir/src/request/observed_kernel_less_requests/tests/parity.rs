// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn whole_original_three_verifier_requests_match_including_no_kernel_status_refusal() {
    let b = fixture();
    let rows = observed(&b).0;
    assert_eq!(authority_rows(&rows).len(), 1);
    assert!(matches!(
        authority_rows(&rows)[0],
        E::TrustVcCertificateNotDischarged {
            status: ProofStatus::Pending,
            ..
        }
    ));
}
#[test]
fn all_five_statuses_still_refuse_without_actual_kernel_authority() {
    for status in [
        ProofStatus::Pending,
        ProofStatus::Failed,
        ProofStatus::Trusted,
        ProofStatus::Discharged,
        ProofStatus::Certified,
    ] {
        let mut b = fixture();
        b.module.proof_obligations[0].status = status;
        let rows = observed(&b).0;
        assert!(
            rows.iter()
                .any(|e| matches!(e,E::TrustVcCertificateNotDischarged{status:s,..}if *s==status))
        );
    }
}
#[test]
fn all_vc_modes_keep_unconditional_status_then_trusted_checks() {
    for mode in [
        Mode::ImportProofCertificates,
        Mode::MergeProofCertificates,
        Mode::DischargeProofObligations,
    ] {
        let mut b = trusted();
        vc(&mut b).mode = mode;
        let rows = observed(&b).0;
        assert!(matches!(
            authority_rows(&rows).as_slice(),
            [
                E::TrustVcCertificateNotDischarged { .. },
                E::TrustedCertificateRejected { .. }
            ]
        ));
    }
}
#[test]
fn trusted_allow_policies_skip_only_the_actual_trusted_rejection() {
    for policy in [
        TrustVcTrustedEvidencePolicy::Reject,
        TrustVcTrustedEvidencePolicy::Allow,
        TrustVcTrustedEvidencePolicy::AllowWithDiagnostic,
    ] {
        let mut b = trusted();
        vc(&mut b).options.trusted_evidence = policy;
        let rows = observed(&b).0;
        assert_eq!(
            rows.iter()
                .filter(|e| matches!(e, E::TrustedCertificateRejected { .. }))
                .count(),
            usize::from(policy == TrustVcTrustedEvidencePolicy::Reject)
        );
        assert_eq!(
            rows.iter()
                .filter(|e| matches!(e, E::TrustVcCertificateNotDischarged { .. }))
                .count(),
            1
        );
    }
}
#[test]
fn last_duplicate_obligation_status_wins_as_in_the_actual_btreemap() {
    let mut b = trusted();
    let mut duplicate = b.module.proof_obligations[0].clone();
    duplicate.status = ProofStatus::Certified;
    b.module.proof_obligations.push(duplicate);
    let rows = observed(&b).0;
    assert!(rows.iter().any(|e| matches!(
        e,
        E::TrustVcCertificateNotDischarged {
            status: ProofStatus::Certified,
            ..
        }
    )));
    let last = b.module.proof_obligations.len() - 1;
    b.module.proof_obligations.swap(0, last);
    let rows = observed(&b).0;
    assert!(rows.iter().any(|e| matches!(
        e,
        E::TrustVcCertificateNotDischarged {
            status: ProofStatus::Pending,
            ..
        }
    )));
}
#[test]
fn unknown_status_skips_status_error_but_does_not_skip_trusted_rejection() {
    let mut b = trusted();
    b.module
        .proof_obligations
        .retain(|o| o.id != ProofId::new(0));
    let rows = observed(&b).0;
    assert!(matches!(
        authority_rows(&rows).as_slice(),
        [E::TrustedCertificateRejected { .. }]
    ));
    assert!(
        rows.iter()
            .any(|e| matches!(e, E::UnknownRequestObligation { .. }))
    );
}
#[test]
fn same_pair_with_wrong_digest_is_not_known_authority_evidence() {
    let mut b = trusted();
    vc(&mut b).certificates[0].evidence_digest = ProofDigest::sha256([87; 32]);
    let rows = observed(&b).0;
    assert!(authority_rows(&rows).is_empty());
    assert!(
        rows.iter()
            .any(|e| matches!(e, E::CertificateDigestMismatch { .. }))
    );
}
#[test]
fn raw_prover_mismatch_is_not_repaired_by_alias_or_normalization() {
    let mut b = trusted();
    vc(&mut b).certificates[0].prover = "TrustVc".into();
    let rows = observed(&b).0;
    assert!(authority_rows(&rows).is_empty());
    assert!(
        rows.iter()
            .any(|e| matches!(e, E::MissingCertificate { .. }))
    );
}
#[test]
fn every_physical_duplicate_vc_certificate_keeps_both_refusal_rows() {
    let mut b = trusted();
    let reference = vc_ref(&b).certificates[0].clone();
    vc(&mut b).certificates = vec![reference; 3];
    let rows = observed(&b).0;
    assert_eq!(authority_rows(&rows).len(), 6);
    assert_eq!(
        rows.iter()
            .filter(|e| matches!(e, E::DuplicateRequestCertificate { .. }))
            .count(),
        2
    );
}
#[test]
fn real_clean_cic_bytes_and_strong_status_remain_non_authority_in_this_build() {
    let mut b = fixture();
    b.module.proof_obligations[0].status = ProofStatus::Certified;
    set_certificate(
        &mut b,
        ProofEvidence::CleanCic {
            term: vec![1, 2, 3],
            context: vec![4],
            lineage: ProofDigest::sha256([1; 32]),
            kernel_recheck: None,
        },
    );
    assert!(observed(&b).0.iter().any(|e| matches!(
        e,
        E::TrustVcCertificateNotDischarged {
            status: ProofStatus::Certified,
            ..
        }
    )));
}
#[test]
fn actual_mc_and_wp_modes_follow_all_common_groups_without_vc_authority_checks() {
    let mut b = fixture();
    b.requests.remove(0);
    for r in &mut b.requests {
        match r {
            NativeVerificationRequest::TrustMc(r) => {
                r.mode = McMode::Pdr;
                r.options.chc.pdr.enabled = false;
                r.options.chc.pdr.max_frames = Some(0);
            }
            NativeVerificationRequest::TrustWp(r) => {
                r.mode = WpMode::StrongestPostcondition;
                r.provenance.replay_context.atoms.clear();
                r.options.emit_verification_conditions = false;
            }
            _ => panic!("non-VC fixture"),
        }
    }
    let rows = observed(&b).0;
    assert!(!rows.is_empty());
    assert!(authority_rows(&rows).is_empty());
}
#[test]
fn actual_cross_request_collision_group_is_last_after_all_physical_requests() {
    let b = bad();
    let rows = observed(&b).0;
    let at = rows
        .iter()
        .position(|e| matches!(e, E::TrustVcObligationBothImportedAndDischarged { .. }))
        .unwrap();
    assert!(
        rows[..at]
            .iter()
            .any(|e| matches!(e, E::TrustedCertificateRejected { .. }))
    );
    assert!(
        rows[at..]
            .iter()
            .all(|e| matches!(e, E::TrustVcObligationBothImportedAndDischarged { .. }))
    );
}
#[test]
fn full_raw_unicode_nul_prover_and_unsigned_ids_are_retained_in_errors() {
    let mut b = trusted();
    let raw = "whole λ\0尾".repeat(300);
    b.module.proof_certificates[0].prover = raw.clone();
    b.module.proof_certificates[0].obligation = ProofId::new(u32::MAX);
    let c = b.module.proof_certificates[0].lineage_ref();
    b.module.proof_obligations[0].id = c.obligation;
    vc(&mut b).id = NativeRequestId::new(u32::MAX);
    vc(&mut b).certificates = vec![c];
    let rows = observed(&b).0;
    assert!(rows.iter().any(|e|matches!(e,E::TrustVcCertificateNotDischarged{request,obligation,prover,..}if request.index()==u32::MAX&&obligation.index()==u32::MAX&&prover==&raw)));
}
#[test]
fn no_requests_still_computes_actual_full_module_certificate_selectors() {
    let mut b = fixture();
    b.requests.clear();
    assert!(observed(&b).0.is_empty());
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut st = State::default();
    st.setup(&b, &mut w).unwrap();
    assert_eq!(st.known.len(), b.module.proof_certificates.len());
    assert_eq!(
        st.known[0].reference,
        b.module.proof_certificates[0].lineage_ref()
    );
    drain(&mut st, &mut w);
    empty(&st);
}
#[test]
fn reverse_full_key_lookup_retains_last_row_and_never_pair_only_matches() {
    // Synthetic private lookup table isolates LAST-map semantics; it does NOT
    // assert construction of a real cryptographic evidence collision.
    let b = trusted();
    let reference = vc_ref(&b).certificates[0].clone();
    let mut st = State {
        known: vec![
            Known {
                reference: reference.clone(),
                trusted: false,
            },
            Known {
                reference: reference.clone(),
                trusted: true,
            },
        ],
        ..State::default()
    };
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert_eq!(st.last_known(&reference, &mut w), Ok(Some(true)));
    let mut wrong = reference.clone();
    wrong.evidence_digest = ProofDigest::sha256([91; 32]);
    assert_eq!(st.last_known(&wrong, &mut w), Ok(None));
    drain(&mut st, &mut w);
    empty(&st);
}
#[test]
fn returned_owned_diagnostics_survive_dropping_whole_source_bundle() {
    let rows = {
        let b = bad();
        observed(&b).0
    };
    assert!(
        rows.iter()
            .any(|e| matches!(e, E::TrustedCertificateRejected { .. }))
    );
    assert!(
        rows.iter()
            .any(|e| matches!(e, E::TrustVcObligationBothImportedAndDischarged { .. }))
    );
}
